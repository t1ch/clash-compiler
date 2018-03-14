{-|
Copyright  :  (C) 2018, Google Inc.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

This module contains:

  * Template Haskell functions for deriving 'BitPack' instances given a
    custom bit representation as those defined in
    'Clash.Annotations.BitRepresentation'.

  * Template Haskell functions for deriving custom bit representations,
    e.g. one-hot, for a data type.

-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveLift         #-}
{-# LANGUAGE MagicHash          #-}
{-# LANGUAGE QuasiQuotes        #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

module Clash.Annotations.BitRepresentation.Deriving
  (
  -- * Derivation functions and their accociated types
    deriveAnnotation
  , deriveDefaultAnnotation
  , derivePackedAnnotation
  , deriveBitPack
  , simpleDerivator
  , packedDerivator
  , dontApplyInHDL
  , ConstructorType(..)
  , FieldsType(..)
  -- * Convenience type synonyms
  , Derivator
  , DataReprAnnExp
  ) where

import Clash.Annotations.BitRepresentation
  (DataReprAnn(..), ConstrRepr(..), BitMask, Value, reprType)
import Clash.Annotations.BitRepresentation.Internal
  (dataReprAnnToDataRepr', thTypeToType', DataRepr'(..), ConstrRepr'(..))
import Clash.Annotations.BitRepresentation.Util
  (bitOrigins, BitOrigin(..), bitRanges, Bit(..))

import           Clash.Class.BitPack        (BitPack, BitSize, pack, unpack)
import           Clash.Class.Resize         (resize)
import           Clash.Sized.BitVector      (BitVector, high, low, (++#))
import           Control.Monad              (zipWithM)
import           Data.Bits
  (shiftL, shiftR, complement, (.&.), (.|.), zeroBits, popCount, bit, testBit)
import           Data.Data                  (Data)
import           Data.List                  (mapAccumL, zipWith4, sortOn)
import           Data.Typeable              (Typeable)
import qualified Data.Map                   as Map
import           Data.Proxy                 (Proxy(..))
import           GHC.Exts                   (Int(I#))
import           GHC.Integer.Logarithms     (integerLog2#)
import           GHC.TypeLits               (natVal)
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

-- | Used to track constructor bits in packed derivation
data BitMaskOrigin
  = External
  -- ^ Constructor bit should be stored externally
  | Embedded BitMask Value
  -- ^ Constructor bit should be stored in one of the constructor's fields
    deriving (Show, Data, Typeable, Lift)

isExternal :: BitMaskOrigin -> Bool
isExternal External = True
isExternal _        = False

type NameMap = Map.Map Name Type

-- | DataReprAnn as template haskell expression
type DataReprAnnExp = Exp

-- | A derivator derives a bit representation given a type
type Derivator = Type -> Q DataReprAnnExp

-- | Indicates how to pack constructor for simpleDerivator
data ConstructorType
  = Binary
  -- ^ First constructor will be encoded as 0b0, the second as 0b1, the third
  -- as 0b10, etc.
  | OneHot
  -- ^ Reserve a single bit for each constructor marker.

-- | Indicates how to pack (constructor) fields for simpleDerivator
data FieldsType
  = Overlap
  -- ^ Store fields of different constructors at (possibly) overlapping bit
  -- positions. That is, a data type with two constructors with each two fields
  -- of each one bit will take /two/ bits for its whole representation (plus
  -- constructor bits). This is the default behaviour of Clash.
  | Wide
  -- ^ Store fields of different constructs at non-overlapping positions. That
  -- is, a data type with two constructors with each two fields of each one bit
  -- will take /four/ bits for its whole representation (plus constructor bits).

-- | Determine most significant bit set for given integer.
--
-- TODO: Current complexity is O(n). We could probably use machine instructions
-- for ~constant complexity.
msb :: Integer -> Integer
msb 0 = error $ "Most significant bit does not exist for zero."
msb 1 = 0
msb n = 1 + msb (shiftR n 1)

-- | Integer version of (ceil . log2). Can handle arguments up to 2^(2^WORDWIDTH).
integerLog2Ceil :: Integer -> Integer
integerLog2Ceil n =
  let nlog2 = fromIntegral $ I# (integerLog2# n) in
  if n > 2^nlog2 then nlog2 + 1 else nlog2

-- | Determine number of bits needed to represent /n/ options
bitsNeeded :: Integer -> Integer
bitsNeeded 0 = 0
bitsNeeded 1 = 1
bitsNeeded n = integerLog2Ceil n

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _k) = n

-- | Replace Vars types given in mapping
resolve :: NameMap -> Type -> Type
resolve nmap (VarT n) = nmap Map.! n
resolve nmap (AppT t1 t2) = AppT (resolve nmap t1) (resolve nmap t2)
resolve _nmap t@(ConT _) = t
resolve _nmap t = error $ "Unexpected type: " ++ show t

resolveCon :: NameMap -> Con -> Con
resolveCon nmap (NormalC t (unzip -> (bangs, fTypes))) =
  NormalC t $ zip bangs $ map (resolve nmap) fTypes
resolveCon _name constr =
  error $ "Unexpected constructor: " ++ show constr

collectTypeArgs :: Type -> (Type, [Type])
collectTypeArgs t@(ConT _name) = (t, [])
collectTypeArgs (AppT t1 t2) =
  let (base, args) = collectTypeArgs t1 in
  (base, args ++ [t2])
collectTypeArgs t =
  error $ "Unexpected type: " ++ show t

-- | Returns size in number of bits of given type. Relies on the presence of a
-- BitSize implementation. Tries to recognize literal values and return a simple
-- expression.
typeSize :: Type -> Q Exp
typeSize typ = do
  bitSizeInstances <- reifyInstances ''BitSize [typ]
  case bitSizeInstances of
    [] ->
      error $ unwords [
          "Could not find custom bit representation nor BitSize instance"
        , "for", show typ ++ "." ]
    [TySynInstD _ (TySynEqn _ (LitT (NumTyLit n)))] ->
      [| n |]
    [_impl] ->
      [| natVal (Proxy :: Proxy (BitSize $(return typ))) |]
    unexp ->
      error $ "Unexpected result from reifyInstances: " ++ show unexp

-- | Generate bitmask from a given bit, with a certain size
bitmask
  :: Integer
  -- ^ Bitmask starts at bit /n/
  -> Integer
  -- ^ Bitmask has size /m/
  -> Integer
bitmask _start 0    = 0
bitmask start  size
  | start < 0        = error $ "Start cannot be <0. Was: " ++ show start
  | size < 0         = error $ "Size cannot be <0. Was: " ++ show size
  | start + 1 < size = error $ "Start + 1 (" ++ show start ++ " - 1) cannot be smaller than size (" ++ show size ++  ")."
  | otherwise        = shiftL (2^size - 1) $ fromIntegral (start - (size - 1))


fieldTypes :: Con -> [Type]
fieldTypes (NormalC _nm bTys) =
  [ty | (_, ty) <- bTys]
fieldTypes (RecC _nm bTys) =
  [ty | (_, _, ty) <- bTys]
fieldTypes (InfixC (_, ty1) _nm (_, ty2)) =
  [ty1, ty2]
fieldTypes con =
  error $ "Unexpected constructor type: " ++ show con

conName :: Con -> Name
conName c = case c of
  NormalC nm _  -> nm
  RecC    nm _  -> nm
  InfixC _ nm _ -> nm
  _ -> error $ "No GADT support"

constrFieldSizes
  :: Con
  -> Q (Name, [Exp])
constrFieldSizes con = do
  fieldSizes <- mapM typeSize (fieldTypes con)
  return (conName con, fieldSizes)

complementInteger :: Int -> Integer -> Integer
complementInteger 0 _i = 0
complementInteger size i =
  let size' = size - 1 in
  if testBit i size' then
    complementInteger size' i
  else
    (.|.) (bit size') (complementInteger size' i)

deriveAnnotation :: Derivator -> Q Type -> Q [Dec]
deriveAnnotation deriv typ =
  return <$> pragAnnD ModuleAnnotation (deriv =<< typ)

--------------------------------------------
------------ SIMPLE DERIVATIONS ------------
--------------------------------------------
buildConstrRepr
  :: Q Exp
  -- ^ Data size (excluding constructor size)
  -> Name
  -- ^ Constr name
  -> [Exp]
  -- ^ Field masks
  -> BitMask
  -- ^ Constructor mask
  -> Value
  -- ^ Constructor value
  -> Q Exp
buildConstrRepr dataSize constrName fieldAnns constrMask constrValue = [|
  ConstrRepr
    constrName
    $mask
    $value
    $(return $ ListE fieldAnns)
  |]
  where
    mask  = [| shiftL constrMask  (fromIntegral $ $dataSize)|]
    value = [| shiftL constrValue (fromIntegral $ $dataSize)|]

countConstructor :: [Integer] -> [(BitMask, Value)]
countConstructor ns = zip (repeat mask) ns
  where
    maskSize = integerLog2Ceil $ maximum ns
    mask = 2^maskSize - 1

oneHotConstructor :: [Integer] -> [(BitMask, Value)]
oneHotConstructor ns = zip values values
  where
    values = [shiftL 1 (fromIntegral n) | n <- ns]

overlapFieldAnns :: [[Exp]] -> [Q [Exp]]
overlapFieldAnns fieldSizess = map go fieldSizess
  where
    fieldSizess'  = ListE $ map ListE fieldSizess
    constructorSizes = [| map sum $(return fieldSizess') |]
    go fieldSizes =
      sequence $
      snd $
      mapAccumL
        (\start size -> ([| $start - $size |], [| bitmask $start $size |]))
        [| maximum $constructorSizes - 1 |]
        (map return fieldSizes)

wideFieldAnns :: [[Exp]] -> [Q [Exp]]
wideFieldAnns fieldSizess = zipWith id (map go constructorOffsets) fieldSizess
  where
    constructorSizes =
      map (AppE (VarE 'sum)) (map ListE fieldSizess)

    constructorOffsets :: [Q Exp]
    constructorOffsets =
      init $
      scanl
        (\offset size -> [| $offset + $size |])
        [| 0 |]
        (map return constructorSizes)

    dataSize = [| sum $(return $ ListE constructorSizes) |]

    go :: Q Exp -> [Exp] -> Q [Exp]
    go offset fieldSizes =
      sequence $
      snd $
      mapAccumL
        (\start size -> ([| $start - $size |], [| bitmask $start $size |]))
        [| $dataSize - 1 - $offset |]
        (map return fieldSizes)

-- | Derive DataRepr' for a specific type.
deriveDataRepr
  :: ([Integer] -> [(BitMask, Value)])
  -- ^ Constructor derivator
  -> ([[Exp]] -> [Q [Exp]])
  -- ^ Field derivator
  -> Derivator
deriveDataRepr constrDerivator fieldsDerivator typ = do
  info <- reify tyConstrName
  case info of
    (TyConI (DataD [] _constrName vars _kind dConstructors _clauses)) ->
      let varMap = Map.fromList $ zip (map tyVarBndrName vars) typeArgs in
      let resolvedConstructors = map (resolveCon varMap) dConstructors in do

      -- Get sizes and names of all constructors
      (constrNames, fieldSizess) <-
        unzip <$> (mapM constrFieldSizes resolvedConstructors)

      let
        (constrMasks, constrValues) =
          unzip $ constrDerivator [0..fromIntegral $ length dConstructors - 1]

      let constrSize    = 1 + (msb $ maximum constrMasks)
      fieldAnns        <- sequence $ fieldsDerivator fieldSizess
      let fieldAnnsFlat = return $ ListE $ concat fieldAnns

      let dataSize | null $ concat fieldAnns = [| 0 |]
                   | otherwise = [| 1 + (msb $ maximum $ $fieldAnnsFlat) |]


      -- Determine at which bits various fields start
      let constrReprs = zipWith4
                          (buildConstrRepr dataSize)
                          constrNames
                          fieldAnns
                          constrMasks
                          constrValues

      [| DataReprAnn
          $(reprType $ return typ)
          ($dataSize + constrSize)
          $(listE constrReprs) |]
    _ ->
      error $ "Could not derive dataRepr for: " ++ show info

    where
      (ConT tyConstrName, typeArgs) = collectTypeArgs typ

-- | Simple derivators change the (default) way Clash stores data types. It
-- assumes no overlap between constructors and fields.
simpleDerivator :: ConstructorType -> FieldsType -> Derivator
simpleDerivator ctype ftype = deriveDataRepr constrDerivator fieldsDerivator
  where
    constrDerivator =
      case ctype of
        Binary -> countConstructor
        OneHot -> oneHotConstructor

    fieldsDerivator =
      case ftype of
        Overlap -> overlapFieldAnns
        Wide -> wideFieldAnns

-- | Derives bit representation corresponding to the default manner in which
-- Clash stores types.
defaultDerivator :: Derivator
defaultDerivator = simpleDerivator Binary Overlap

-- | Derives bit representation corresponding to the default manner in which
-- Clash stores types.
deriveDefaultAnnotation :: Q Type -> Q [Dec]
deriveDefaultAnnotation = deriveAnnotation defaultDerivator

---------------------------------------------------------
------------ DERIVING PACKED REPRESENTATIONS ------------
---------------------------------------------------------
packedConstrRepr
  :: Int
  -- ^ Data width
  -> Integer
  -- ^ External constructor width
  -> Integer
  -- ^ nth External so far
  -> [(BitMaskOrigin, ConstrRepr)]
  -> [ConstrRepr]
packedConstrRepr _ _ _ [] = []
packedConstrRepr dataWidth constrWidth n ((External, ConstrRepr name _ _ anns) : constrs) =
  constr : packedConstrRepr dataWidth constrWidth (n+1) constrs
  where
    constr =
      ConstrRepr
        name
        (shiftL (2^constrWidth - 1) dataWidth)
        (shiftL n dataWidth)
        anns

packedConstrRepr dataWidth constrWidth n ((Embedded mask value, ConstrRepr name _ _ anns) : constrs) =
  constr : packedConstrRepr (fromIntegral dataWidth) constrWidth n constrs
  where
    constr =
      ConstrRepr
        name
        mask
        value
        anns

packedDataRepr
  :: Type
  -> Integer
  -> [(BitMaskOrigin, ConstrRepr)]
  -> DataReprAnn
packedDataRepr typ dataWidth constrs =
  DataReprAnn
    typ
    (dataWidth + constrWidth)
    (packedConstrRepr (fromIntegral dataWidth) constrWidth 0 constrs)
  where
    external    = filter isExternal (map fst constrs)
    constrWidth = bitsNeeded $ toInteger $ length external

-- | Try to distribute constructor bits over fields
storeInFields
  :: Int
  -- ^ data width
  -> BitMask
  -- ^ Additional mask gathered so far
  -> [BitMask]
  -- ^ Repr bitmasks to try and pack
  -> [BitMaskOrigin]
storeInFields _dataWidth _additionalMask [] = []
storeInFields _dataWidth _additionalMask [_] =
  -- Last constructor is implict
  [Embedded 0 0]
storeInFields dataWidth additionalMask constrs =
  if commonMask == fullMask then
    -- We can't store the constructor anywhere special, so we need a special
    -- constructor bit stored besides fields
    External : storeInFields dataWidth additionalMask (tail constrs)
  else
    -- Hooray, we can store it somewhere.
    maskOrigins ++ (storeInFields dataWidth additionalMask' (drop storeSize constrs))

  where
    headMask   = head constrs
    commonMask = (.|.) headMask additionalMask

    -- Variables for the case that we can store something:
    storeMask       = complementInteger dataWidth commonMask
    additionalMask' = (.|.) additionalMask storeMask
    storeSize       = 2^(popCount storeMask) - 1
    maskOrigins     = [Embedded storeMask (toInteger n) | n <- [1..storeSize]]

    -- BitMask which spans the complete data size
    fullMask = 2^dataWidth - 1

derivePackedAnnotation' :: DataReprAnn -> DataReprAnn
derivePackedAnnotation' (DataReprAnn typ size constrs) =
  dataRepr
  where
    constrWidth = bitsNeeded $ toInteger $ length constrs
    dataWidth   = size - constrWidth
    fieldMasks  = [foldl (.|.) zeroBits anns | ConstrRepr _ _ _ anns <- constrs]

    -- Default annotation will overlap "to the left", so sorting on size will
    -- actually provide us with the 'fullest' constructors first and the
    -- 'empties' last.
    sortedMasks = reverse $ sortOn fst $ zip fieldMasks constrs
    origins     = storeInFields (fromInteger dataWidth) zeroBits (map fst sortedMasks)
    constrs'    = zip origins $ map snd sortedMasks
    dataRepr    = packedDataRepr typ dataWidth constrs'

-- | This derivator tries to distribute its constructor bits over space left
-- by the difference in constructor sizes. Example:
--
-- @
-- type SmallInt = Unsigned 2
--
-- data Train
--    = Passenger SmallInt
--    | Freight SmallInt SmallInt
--    | Maintenance
--    | Toy
-- @
--
-- The packed representation of this data type needs only a single constructor
-- bit. The first bit discriminates between @Freight@ and non-@Freight@
-- constructors. All other constructors do not use their last two bits; the
-- packed representation will store the rest of the constructor bits there.
packedDerivator :: Derivator
packedDerivator typ =
  [| derivePackedAnnotation' $(defaultDerivator typ ) |]

derivePackedAnnotation :: Q Type -> Q [Dec]
derivePackedAnnotation = deriveAnnotation packedDerivator

----------------------------------------------------
------------ DERIVING BITPACK INSTANCES ------------
----------------------------------------------------

-- | Collect data reprs of current module
collectDataReprs :: Q [([Name], DataRepr')]
collectDataReprs = do
  thisMod <- thisModule
  (map toDataRepr') <$> reifyAnnotations (AnnLookupModule thisMod)
  where
    toDataRepr' :: DataReprAnn -> ([Name], DataRepr')
    toDataRepr' dataRepr@(DataReprAnn _ _ constrs) =
      ( [n | ConstrRepr n _ _ _ <- constrs]
      , dataReprAnnToDataRepr' dataRepr
      )

group :: [Bit] -> [(Int, Bit)]
group [] = []
group bs = (length head', head bs) : rest
  where
    tail' = dropWhile (==head bs) bs
    head' = takeWhile (==head bs) bs
    rest  = group tail'

bitToExpr' :: (Int, Bit) -> Q Exp
bitToExpr' (0, _) = error $ "Unexpected group length: 0"
bitToExpr' (1, H) = lift high
bitToExpr' (1, L) = lift low
-- TODO / Evaluate: Undefined bit values should not be converted
bitToExpr' (1, _) = lift low
bitToExpr' (numTyLit' -> n, H) =
  [| complement (resize $(lift low) :: BitVector $n) |]
bitToExpr' (numTyLit' -> n, L) =
  [| resize $(lift low) :: BitVector $n |]
bitToExpr' (numTyLit' -> n, _) =
  [| resize $(lift low) :: BitVector $n |]

bitsToExpr :: [Bit] -> Q Exp
bitsToExpr [] = error $ "Unexpected empty bit list"
bitsToExpr bits =
  foldl1
    (\v1 v2 -> [| $v1 ++# $v2 |])
    (map bitToExpr' $ group bits)

numTyLit' :: Integral a => a -> Q Type
numTyLit' n = LitT <$> (numTyLit $ fromIntegral n)

-- | Select a list of ranges from a bitvector expression
select'
  :: Exp
  -> [(Int, Int)]
  -> Q Exp
select' _vec [] =
  error $ "Unexpected empty list of intervals"
select' vec ranges =
  foldl1 (\v1 v2 -> [| $v1 ++# $v2 |]) $ map (return . select'') ranges
    where
      select'' :: (Int, Int) -> Exp
      select'' (from, downto) =
        let size = from - downto + 1 in
        let
          shifted
            | downto == 0 =
                vec
            | otherwise =
                AppE
                  (AppE (VarE 'shiftR) vec)
                  (LitE $ IntegerL $ fromIntegral downto) in

        SigE
          -- Select from whole vector
          (AppE (VarE 'resize) shifted)
          -- Type signature:
          (AppT (ConT ''BitVector) (LitT $ NumTyLit $ fromIntegral size))

-- | Select a range (bitorigin) from a bitvector
select
  :: [Exp]
  -- ^ BitVectors of fields
  -> BitOrigin
  -- ^ Select bits
  -> Q Exp
select _fields (Lit []) =
  error $ "Unexpected empty literal."
select _fields (Lit lits) = do
  let size = fromIntegral $ length lits
  vec <- bitsToExpr lits
  return $ SigE
            -- Apply bLit to literal string
            vec
            -- Type signature:
            (AppT (ConT ''BitVector) (LitT $ NumTyLit size))

select fields (Field fieldn from downto) =
  select' (fields !! fieldn) [(from, downto)]

buildPackMatch
  :: DataRepr'
  -> ConstrRepr'
  -> Name
  -> Q Match
buildPackMatch dataRepr cRepr@(ConstrRepr' _ _ _ _ fieldanns) qName = do
  fieldNames <-
    mapM (\n -> newName $ "field" ++ show n) [0..length fieldanns-1]
  fieldPackedNames <-
    mapM (\n -> newName $ "fieldPacked" ++ show n) [0..length fieldanns-1]

  let packed fName = AppE (VarE 'pack) (VarE fName)
  let pack' pName fName = ValD (VarP pName) (NormalB $ packed fName) []
  let fieldPackedDecls = zipWith pack' fieldPackedNames fieldNames
  let origins = bitOrigins dataRepr cRepr

  vec <- foldl1
              (\v1 v2 -> [| $v1 ++# $v2 |])
              (map (select $ map VarE fieldPackedNames) origins)

  return $ Match (ConP qName (VarP <$> fieldNames)) (NormalB vec) fieldPackedDecls

-- | Build a /pack/ function corresponding to given DataRepr
buildPack
  :: [Name]
  -> DataRepr'
  -> Q [Dec]
buildPack constrNames dataRepr@(DataRepr' _name _size constrs) = do
  argNameIn    <- newName "toBePackedIn"
  argName      <- newName "toBePacked"
  constrs'     <- zipWithM (buildPackMatch dataRepr) constrs constrNames
  let packBody    = CaseE (VarE argName) constrs'
  let packLambda  = LamE [VarP argName] packBody
  let packApplied = (VarE 'dontApplyInHDL) `AppE` packLambda `AppE` (VarE argNameIn)
  let func        = FunD 'pack [Clause [VarP argNameIn] (NormalB packApplied) []]
  return [func]


-- | In Haskell apply the first argument to the second argument,
--   in HDL just return the second argument.
--
-- This is used in the generated pack/unpack to not do anything in HDL.
dontApplyInHDL :: (a -> b) -> a -> b
dontApplyInHDL f a = f a
{-# NOINLINE dontApplyInHDL #-}


buildUnpackField
  :: Name
  -> Integer
  -> Q Exp
buildUnpackField valueName mask =
  let ranges = bitRanges mask in
  let vec = select' (VarE valueName) ranges in
  [| unpack $vec |]

buildUnpackIfE
  :: Name
  -> ConstrRepr'
  -> Name
  -> Q (Guard, Exp)
buildUnpackIfE valueName (ConstrRepr' _ _ mask value fieldanns) qName = do
  let valueName' = return $ VarE valueName
  guard  <- NormalG <$> [| ((.&.) $valueName' mask) == value |]
  fields <- mapM (buildUnpackField valueName) fieldanns
  return (guard, foldl AppE (ConE qName) fields)

-- | Build an /unpack/ function corresponding to given DataRepr
buildUnpack
  :: [Name]
  -> DataRepr'
  -> Q [Dec]
buildUnpack constrNames (DataRepr' _name _size constrs) = do
  argNameIn   <- newName "toBeUnpackedIn"
  argName     <- newName "toBeUnpacked"
  matches     <- zipWithM (buildUnpackIfE argName) constrs constrNames
  err         <- [| error $ "Could not match constructor for: " ++ show $(varE argName) |]
  let unpackBody    = MultiIfE $ matches ++ [(NormalG (ConE 'True), err)]
  let unpackLambda  = LamE [VarP argName] unpackBody
  let unpackApplied = (VarE 'dontApplyInHDL) `AppE` unpackLambda `AppE` (VarE argNameIn)
  let func          = FunD 'unpack [Clause [VarP argNameIn] (NormalB unpackApplied) []]
  return [func]

-- | Derives BitPack instances for given type. Will account for custom bit
-- representation annotations in the module where the splice is ran. Note that
-- the generated instance might conflict with existing implementations (for
-- example, an instance for /Maybe a/ exists, yielding conflicts for any
-- alternative implementations).
deriveBitPack :: Q Type -> Q [Dec]
deriveBitPack typQ = do
  anns <- collectDataReprs
  typ  <- typQ
  let typ' = thTypeToType' typ

  let ann = case filter (\(_names, DataRepr' t _ _) -> t == typ') anns of
              [a] -> a
              []  -> error $ "No custom bit annotation found."
              _   -> error $ "Overlapping bit annotations found."

  packFunc   <- (uncurry buildPack) ann
  unpackFunc <- (uncurry buildUnpack) ann

  let (DataRepr' _name dataSize _constrs) = snd ann

  let bitSizeInst = TySynInstD
                      ''BitSize
                      (TySynEqn
                        [typ]
                        (LitT (NumTyLit $ fromIntegral dataSize)))

  let bpInst = [ InstanceD
                   (Just Overlapping)
                   -- Overlap
                   []
                   -- Context
                   (AppT (ConT ''BitPack) typ)
                   -- Type
                   (bitSizeInst : packFunc ++ unpackFunc)
                   -- Declarations
               ]
  alreadyIsInstance <- isInstance ''BitPack [typ]
  if alreadyIsInstance then
    error $ show typ ++ " already has a BitPack instance."
  else
    return bpInst
