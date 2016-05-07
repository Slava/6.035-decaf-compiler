{-# OPTIONS -Wall #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module LLIR where

-- Imports
import Prelude
import Data.List
import Data.Maybe
import Text.Printf (printf)

--import ParseTypes
import qualified Data.Map as HashMap


data VType            = TInt
                      | TBool
                      | TString
                      | TFunction VType [VType]
                      | TVoid
                      | TCallout
                      | TArray VType
                      | TPointer VType
                      deriving (Eq, Show);

{- in bytes -}
typeSize :: VType -> Int
typeSize op = case op of
  TInt       -> 8
  TBool      -> 8 -- todo fix to 1
  TString    -> 8 -- ptr
  TPointer _ -> 8 -- ptr
  TFunction _ _ -> 8 -- ptr
  TVoid      -> 0 -- ptr
  TCallout   -> 8 -- ptr
  TArray x   -> 8 -- ptr


getDerivedType :: VType -> Maybe VType
getDerivedType a =
  case a of
    TPointer ty -> Just ty
    _ -> Nothing

getDerivedTypeN :: VType -> VType
getDerivedTypeN a =
  case a of
    TPointer ty -> ty
    _ -> TVoid

getArrayType :: VType -> Maybe VType
getArrayType a =
  case a of
    TArray ty -> Just ty
    _ -> Nothing

class Namable a where
  getName :: a -> String

class Locationable a where
  setInsertionPoint :: a -> Builder -> Builder

class Value a where
  getType :: Builder -> a -> VType
  valueEq :: VFunction -> a -> a -> Bool

instance Value String where
  getType _ a = TString
  valueEq _ a b = a == b

data ValueRef = InstRef String
              | ConstInt Integer
              | ConstString String
              | ConstBool Bool
              | CalloutRef String
              | GlobalRef String
              | FunctionRef String
              | ArgRef Int String
              | Temp String
  deriving(Eq, Show, Ord);

getReferenceName :: ValueRef -> String
getReferenceName (InstRef a) = a
getReferenceName (ConstInt _) = "!cint"
getReferenceName (ConstString _) = "!cstring"
getReferenceName (ConstBool _) = "!cbool"
getReferenceName (CalloutRef a) = a
getReferenceName (GlobalRef a) = a
getReferenceName (FunctionRef a) = a
getReferenceName (ArgRef _ _) = "!argref"

instance Value ValueRef where
  getType builder (InstRef str) =
    case getInstruction builder str of
      Just inst -> getType builder inst
      Nothing -> TVoid
  getType _ (ConstInt _) = TInt
  getType _ (ConstBool _) = TBool
  getType builder (GlobalRef str) =
    case HashMap.lookup str (globals $ pmod builder) of
      Just (a,Nothing) -> TPointer a
      Just (a,Just _) -> TArray a
      Nothing -> TVoid

  getType _ (ConstString _) = TString
  getType _ (CalloutRef _) = TCallout
  getType builder (FunctionRef str) =
    case getFunction builder str of
      Just func -> getType builder func
      Nothing -> TVoid
  getType builder (ArgRef idx str) =
    case do
      func <- getFunction builder str
      let args :: [VType] = arguments func
      if idx < length args then Just $ args !! idx else Nothing
    of
      Just t -> t
      Nothing -> TVoid

  valueEq builder (InstRef str1) (InstRef str2) =
    case do
      inst1 <- HashMap.lookup str1 (functionInstructions builder) 
      inst2 <- HashMap.lookup str2 (functionInstructions builder) 
      return $ valueEq builder inst1 inst2
    of
      Just a -> a
      Nothing -> False
  valueEq builder (ConstInt a) (ConstInt b) = a == b
  valueEq builder (ConstString a) (ConstString b) = a == b
  valueEq builder (ConstBool a) (ConstBool b) = a == b
  valueEq builder (CalloutRef a) (CalloutRef b) = a == b
  valueEq builder (GlobalRef a) (GlobalRef b) = a == b
  valueEq builder (FunctionRef a) (FunctionRef b) = a == b
  valueEq builder (ArgRef a1 b1) (ArgRef a2 b2) = (a1 == a2) && (b1 == b2)
  valueEq builder _ _ = False

data VInstruction = VUnOp {- name -} String {- operand -} String {- argument name -} ValueRef
                  | VBinOp {- name -} String {- operand -} String {- argument name -} ValueRef ValueRef
                  | VStore  String {- tostore -} ValueRef {- location -} ValueRef
                  | VLookup String ValueRef
                  | VAllocation String {- type -} VType {- if array -} (Maybe Int)
                  | VArrayStore String {- tostore -} ValueRef {- array -} ValueRef {- idx -} ValueRef
                  | VArrayLookup String {- array -} ValueRef {- idx -} ValueRef
                  | VArrayLen String ValueRef
                  | VReturn String (Maybe ValueRef)
                  | VCondBranch String {-cond-} ValueRef {-true-} String {-false-} String
                  | VUnreachable String
                  | VUncondBranch String String
                  | VMethodCall String {- is-callout? -} Bool {- fname -} String {- args -} [ValueRef]
                  | VPHINode {- name -} String (HashMap.Map {- block predecessor -} String {- value -} ValueRef)
  deriving (Eq, Show);

getPHIMap (VPHINode _ a) = a

getLastStore :: VInstruction -> [VInstruction] -> Maybe VInstruction
getLastStore instr instrs =
    let instrRef = InstRef $ getName instr
        in foldr (\i acc -> case acc of
            Just a -> acc
            Nothing -> case i of
                VStore _ _ sloc -> if sloc == instrRef then Just i else Nothing
                _ -> Nothing) Nothing instrs

getLastOther :: VInstruction -> [VInstruction] -> Maybe VInstruction
getLastOther instr instrs =
    let instrRef = InstRef $ getName instr
      in  foldr (\i acc -> case acc of
            Just a -> acc
            Nothing ->
              let used = (getUsed i)
                  usedThis = any (\x -> (useInstruction x) == (getName instr)) used
                  in if (not usedThis) then Nothing
                    else case i of
                      VStore _ _ sloc -> if sloc == instrRef then Nothing else Just i
                      VLookup _ sloc -> if sloc == instrRef then Nothing else Just i
                      _ -> Just i
          ) Nothing instrs

instance Namable VInstruction where
  getName (VUnOp name _ _ ) = name
  getName (VBinOp name _ _ _ ) = name
  getName (VStore name _ _) = name
  getName (VLookup name _) = name
  getName (VAllocation name _ _) = name
  getName (VArrayStore name _ _ _) = name
  getName (VArrayLookup name _ _) = name
  getName (VArrayLen name _) = name
  getName (VReturn name _) = name
  getName (VCondBranch name _ _ _) = name
  getName (VUncondBranch name _) = name
  getName (VMethodCall name _ _ _) = name
  getName (VUnreachable name ) = name
  getName (VPHINode name _) = name

instance Value VInstruction where
  getType _ (VUnOp _ op _ )
    | op == "-"   =  TInt
    | op == "!"   =  TBool
  getType _ (VBinOp _ op _ _)
    | op == "+"   =  TInt
    | op == "-"   =  TInt
    | op == "*"   =  TInt
    | op == "/"   =  TInt
    | op == "%"   =  TInt
    | op == "<"   =  TBool
    | op == ">"   =  TBool
    | op == ">="  =  TBool
    | op == "<="  =  TBool
    | op == "u<"   =  TBool
    | op == "u>"   =  TBool
    | op == "u>="  =  TBool
    | op == "u<="  =  TBool
    | op == "=="  =  TBool
    | op == "!="  =  TBool
    | op == "&"  =  TBool
    | op == "|"  =  TBool
  getType _ (VUnreachable _) = TVoid
  getType _ (VStore _ toStore _) = TVoid
  getType b (VLookup _ toLookup) =
    case getDerivedType $ getType b toLookup of
      Just a -> a
      Nothing -> TVoid
  getType _ (VAllocation _ a Nothing) = TPointer a
  getType _ (VAllocation _ a (Just _) ) = TArray a

  getType _ (VArrayStore _ _ _ _) = TVoid
  getType b (VArrayLookup _ toLookup _ ) =
    case getArrayType $ getType b toLookup of
      Just a -> a
      Nothing -> TVoid

  getType _ (VArrayLen _ _ ) = TInt
  getType b (VPHINode _ vals ) =
    let ems :: [ValueRef] = HashMap.elems vals
    in case ems of
      [] -> TVoid
      a -> getType b (head a)

  getType _ (VReturn _ _ ) = TVoid
  getType _ (VCondBranch _ _ _ _) = TVoid
  getType _ (VUncondBranch _ _) = TVoid
  getType _ (VMethodCall _ True _ _) = TInt
  getType b (VMethodCall _ False name _) =
    case HashMap.lookup name $ (functions . pmod) b of
      Nothing -> TVoid
      Just a -> returnType a

  valueEq b (VUnOp _ op1 arg1) (VUnOp _ op2 arg2) = ( op1 == op2 ) && ( arg1 == arg2 )
  valueEq b (VBinOp _ op1 a1 b1) (VBinOp _ op2 a2 b2) = ( op1 == op2 ) && ( a1 == a2 ) && ( b1 == b2 )
  valueEq b (VArrayLen _ op1 ) (VArrayLen _ op2) = ( op1 == op2 )
  valueEq b (VPHINode _ a1 ) (VPHINode _ a2) = ((HashMap.keys a1) == (HashMap.keys a2) ) && all (\x -> ( hml a1 x "veq1" ) == ( hml a2 x "veq2" ) ) (HashMap.keys a1)
  valueEq b (VArrayLen _ a1 ) (VArrayLen _ a2) = a1 == a2

  valueEq b _ _ = False

safeBangBang :: [a] -> Int -> Maybe a
safeBangBang list index = case (length list) > index of
    True -> Just $ list !! index
    False -> Nothing

opCount :: VInstruction -> Int
opCount (VUnOp _ _ _) = 1
opCount (VBinOp _ _ _ _) = 2
opCount (VStore _ _ _) = 2
opCount (VLookup _ _) = 1
opCount (VArrayStore _ _ _ _) = 3
opCount (VArrayLookup _ _ _) = 2
opCount (VArrayLen _ _) = 1
opCount (VReturn _ (Just a)) = 1
opCount (VReturn _ Nothing) = 0
opCount (VCondBranch _ _ _ _) = 1
opCount (VMethodCall _ _ _ vals) = 1 + length vals
opCount (VPHINode _ valMap) = length (HashMap.elems valMap)
opCount _ = 0

getOp :: VInstruction -> Int -> Maybe ValueRef
getOp (VUnOp _ _ val0) 0 = Just val0
getOp (VBinOp _ _ val0 _) 0 = Just val0
getOp (VBinOp _ _ _ val1) 1 = Just val1
getOp (VStore _ val0 _) 0 = Just val0
getOp (VStore _ _ val1) 1 = Just val1
getOp (VLookup _ val0) 0 = Just val0
getOp (VArrayStore _ val0 _ _) 0 = Just val0
getOp (VArrayStore _ _ val1 _) 1 = Just val1
getOp (VArrayStore _ _ _ val2) 2 = Just val2
getOp (VArrayLookup _ val0 _) 0 = Just val0
getOp (VArrayLookup _ _ val1) 1 = Just val1
getOp (VArrayLen _ val0) 0 = Just val0
getOp (VReturn _ val0) 0 = val0
getOp (VCondBranch _ val0 _ _) 0 = Just val0
getOp (VMethodCall _ isCallout fname vals) i =
  if i==0 then
    Just $ if isCallout then CalloutRef fname else FunctionRef fname
  else
    safeBangBang vals (i-1)
getOp (VPHINode _ valMap) i = safeBangBang (HashMap.elems valMap) i
getOp _ _ = Nothing

replaceOp :: VInstruction -> Int -> ValueRef -> VInstruction
replaceOp (VUnOp a b _) 0 nval = (VUnOp a b nval)
replaceOp (VBinOp a b _ val1) 0 nval = (VBinOp a b nval val1)
replaceOp (VBinOp a b val0 _) 1 nval = (VBinOp a b val0 nval)
replaceOp (VStore a _ val1) 0 nval = (VStore a nval val1)
replaceOp (VStore a val0 _) 1 nval = (VStore a val0 nval)
replaceOp (VLookup a _) 0 nval = (VLookup a nval)
replaceOp (VArrayStore a _ val1 val2) 0 nval = (VArrayStore a nval val1 val2)
replaceOp (VArrayStore a val0 _ val2) 1 nval = (VArrayStore a val0 nval val2)
replaceOp (VArrayStore a val0 val1 _) 2 nval = (VArrayStore a val0 val1 nval)
replaceOp (VArrayLookup a _ val1) 0 nval = (VArrayLookup a nval val1)
replaceOp (VArrayLookup a val0 _) 1 nval = (VArrayLookup a val0 nval)
replaceOp (VArrayLen a _) 0 nval = (VArrayLen a nval)
replaceOp (VReturn a _) 0 nval = (VReturn a (Just nval))
replaceOp (VCondBranch a _ b c) 0 nval = (VCondBranch a nval b c)
replaceOp (VMethodCall a b c vals) 0 (CalloutRef fname) = (VMethodCall a True fname vals)
replaceOp (VMethodCall a b c vals) 0 (FunctionRef fname) = (VMethodCall a False fname vals)
replaceOp (VMethodCall a b c vals) 0 _ = error "invalid replacement of function call"
replaceOp (VMethodCall a b c vals) ij nval = let i = ij - 1 in (VMethodCall a b c (take i vals ++ [nval] ++ drop (i + 1) vals))
replaceOp (VPHINode a valMap) i nval = case (safeBangBang (HashMap.keys valMap) i) of
    Just key -> (VPHINode a $ HashMap.insert key nval valMap)
    Nothing -> (VPHINode a valMap)
replaceOp a _ _ = a

-- builder name of instruction int valueref returns builder
replaceInstrOp :: VFunction -> String -> Int -> ValueRef -> VFunction
replaceInstrOp func instrName index nval =
  case do
    instr <- HashMap.lookup instrName (functionInstructions func)
    let newOp = replaceOp instr index nval
    let newInstrs :: HashMap.Map String VInstruction = HashMap.insert instrName newOp (functionInstructions func)
    return $ func{functionInstructions=newInstrs}
  of
    Just a -> a
    Nothing -> func

data Use = Use {
  useInstruction :: String,
  useIndex :: Int
} deriving(Eq, Show);


replaceUse :: VFunction -> Use -> ValueRef -> VFunction
replaceUse func use val = replaceInstrOp func (useInstruction use) (useIndex use) val

replaceAllUses :: VFunction -> VInstruction -> ValueRef -> VFunction
replaceAllUses func instr val =
    let uses = getUses instr func
        in foldl (\acc use -> replaceUse acc use val) func uses

replaceBlockUses :: VFunction -> VInstruction -> [String] -> ValueRef -> VFunction
replaceBlockUses func instr blocks val =
    let uses = getBlockUses instr func blocks
        in foldl (\acc use -> replaceUse acc use val) func uses

deleteAllUses :: VFunction -> VInstruction -> VFunction
deleteAllUses sfunc instr =
    let uses = getUses instr sfunc
        in foldl (\func use ->
          case getUseInstr func use of
            Just inst -> deleteInstruction inst func
            Nothing -> func) sfunc uses

getUseInstr :: VFunction -> Use -> Maybe VInstruction
getUseInstr func use = HashMap.lookup (useInstruction use) (functionInstructions func)

getUseInstr2 :: VFunction -> Use -> VInstruction
getUseInstr2 func use = hml (functionInstructions func) (useInstruction use) "getUseInstr2"

getUseValue :: VFunction -> Use -> Maybe ValueRef
getUseValue func use =
    do
      inst <- HashMap.lookup (useInstruction use) (functionInstructions func)
      val <- getOp inst (useIndex use)
      return $ val

setUseValue :: VFunction -> Use -> ValueRef -> VFunction
setUseValue func use val = replaceInstrOp func (useInstruction use) (useIndex use) val

-- get all uses that this instruction uses (ie all things this instruction depends on)
getUsed :: VInstruction -> [Use]
getUsed inst =
  map (\idx -> ( Use (getName inst) idx) ) [0..(opCount inst)]

-- get all uses that this instruction is used by (ie all things this function is depended on)
getUses :: VInstruction -> VFunction -> [Use]
getUses inst func =
  let instM = (functionInstructions func)
      isValid :: (Use -> Maybe Use) = \mval -> do
          val <- getUseValue func mval
          ninst <- case val of
            InstRef a -> HashMap.lookup a instM
            _ -> Nothing
          if inst == ninst then Just mval else Nothing
      in concat $ map (\inst -> mapMaybe isValid (getUsed inst)) $ HashMap.elems instM

-- get all uses that this instruction is used by (ie all things this function is depended on)
getUsesValRef :: ValueRef -> VFunction -> [Use]
getUsesValRef vref func =
  let instM = (functionInstructions func)
      isValid :: (Use -> Maybe Use) = \mval -> do
          val <- getUseValue func mval
          if val == vref then Just mval else Nothing
      in concat $ map (\inst -> mapMaybe isValid (getUsed inst)) $ HashMap.elems instM

-- get all uses that this instruction is used by (ie all things this function is depended on)
getBlockUses :: VInstruction -> VFunction -> [String] -> [Use]
getBlockUses inst func blks =
  let instM = HashMap.intersection (functionInstructions func) (HashMap.fromList $ zip (concat $ map ( blockInstructions . ( \x -> hml (blocks func) x "getBU" ) ) blks ) [0..] )
      isValid :: (Use -> Maybe Use) = \mval -> do
          val <- getUseValue func mval
          ninst <- case val of
            InstRef a -> HashMap.lookup a (functionInstructions func)
            _ -> Nothing
          if inst == ninst then Just mval else Nothing
      in concat $ map (\inst -> mapMaybe isValid (getUsed inst)) $ HashMap.elems instM

-- get all uses that this instruction is used by (ie all things this function is depended on)
getBlockUsesValRef :: ValueRef -> VFunction -> [String] -> [Use]
getBlockUsesValRef vref func blks=
  let instM = HashMap.intersection (functionInstructions func) (HashMap.fromList $ zip (concat $ map ( blockInstructions . ( \x -> hml (blocks func) x "getBUVR" ) ) blks ) [0..] )
      isValid :: (Use -> Maybe Use) = \mval -> do
          val <- getUseValue func mval
          if val == vref then Just mval else Nothing
      in concat $ map (\inst -> mapMaybe isValid (getUsed inst)) $ HashMap.elems instM

instCast :: VFunction -> ValueRef -> Maybe VInstruction
instCast f (InstRef a) = HashMap.lookup a (functionInstructions f)
instCast _ _  = Nothing

noMaybe :: Maybe a -> a
noMaybe (Just a) = a
noMaybe Nothing = error "bad maybe"

instCastU :: VFunction -> ValueRef -> VInstruction
instCastU f i = noMaybe $ instCast f i

getPHIs :: VFunction -> String -> [VInstruction]
getPHIs fun blk =
  let instmap = functionInstructions fun
      insts = map (\x -> hml instmap x "getPhis1") $ blockInstructions $ (hml (blocks fun) blk "getPhis2")
      in filter (\x -> case x of
        VPHINode _ _ -> True
        _ -> False) insts

getArrayAllocas :: VFunction -> [VInstruction]
getArrayAllocas fun =
  let instmap = functionInstructions fun
      insts = HashMap.elems instmap
      in filter (\x -> case x of
        VAllocation _ _ (Just a) -> True
        _ -> False) insts

getAllocas :: VFunction -> [VInstruction]
getAllocas fun =
  let instmap = functionInstructions fun
      insts = HashMap.elems instmap
      in filter (\x -> case x of
        VAllocation _ _ z -> (z == Nothing)
        _ -> False) insts

data VCallout = VCallout String
  deriving(Eq, Show);

instance Value VCallout where
  getType _ _ = TCallout
  valueEq _ a b = a == b

instance Namable VCallout where
  getName (VCallout name) = name

data VFunction    = VFunction {
  functionName      :: String,
  returnType        :: VType,
  arguments         :: [VType],
  functionInstructions :: HashMap.Map String VInstruction,
  blocks    :: HashMap.Map String VBlock,
  blockOrder :: [String]
} deriving (Eq);

deleteBlockNI :: VBlock -> VFunction -> VFunction
deleteBlockNI block func =
  let name = getName block
      blcks = HashMap.delete name $ blocks func
      succs = (map (\x -> hml (blocks func) x "delNI" ) $ filter (\x -> (x /= name) && HashMap.member x (blocks func) ) $ blockSuccessors block)
      f1 = func{blocks=blcks, blockOrder=delete name (blockOrder func)}
      rf :: VFunction -> VBlock -> VFunction = \f b -> removePredecessor b name f
      f2 = foldl rf f1 succs
      in f2

deleteBlock :: VBlock -> VFunction -> VFunction
deleteBlock block func =
  let name = getName block
      insts :: HashMap.Map String VInstruction = HashMap.filterWithKey (\k v -> not $ elem k (blockInstructions block) ) (functionInstructions func)
      blcks = HashMap.delete name $ blocks func
      succs :: [VBlock] = (map (\x -> hml (blocks func) x "delB" ) $ filter (\x -> (x /= name) && HashMap.member x (blocks func) ) $ blockSuccessors block)
      f1 = func{blocks=blcks, functionInstructions=insts, blockOrder=delete name (blockOrder func)}
      rf :: VFunction -> VBlock -> VFunction = \f b -> removePredecessor b name f
      f2 = foldl rf f1 succs
      in f2

removePredecessor :: VBlock -> String -> VFunction -> VFunction
removePredecessor block pred func =
  let npred = delete pred (blockPredecessors block)
      block2 = block{blockPredecessors=npred}
      f0 = updateBlockF block2 func
      blockName = getName block2
      phis :: [VInstruction] = getPHIs func blockName
      in if ( blockName == pred ) || ( (length npred) == 0 ) then
          deleteBlock block2 f0
        else if (length npred) == 1 then
        -- nuke phis
          let tp = npred !! 0
              fx :: VFunction -> VInstruction -> VFunction = ( replaceAndRemoveF (\(VPHINode _ mp ) -> hml mp tp "llir rpred") )
              f1 :: VFunction = foldl fx f0 phis
              in --if blockName /= "ifFalse" then error $ printf "phis:%s\n prev:%s\n f1:%s\n" (show phis) (show func) (show f1) else 
                 f1
        else
          let f1 = foldl (\f phi@(VPHINode n mp ) ->
                   let vals = HashMap.elems mp
                       nphi :: [ValueRef] = filter (\x -> x /= (InstRef $ n) ) vals
                       in if all (== head nphi) (tail nphi) then
                            replaceAndRemove (head nphi) f phi
                          else
                            updateInstructionF (VPHINode n $ HashMap.delete pred mp) f ) f0 phis
              in f1
-- -}

getParentBlock :: VInstruction -> VFunction -> VBlock
getParentBlock inst func =
  head $ filter (\x -> elem (getName inst) (blockInstructions x) ) (HashMap.elems $ blocks func)

getInstructionsBefore :: VFunction -> VInstruction -> [VInstruction]
getInstructionsBefore func instr =
    case do
        let blockName = getInstructionParent func instr
        block <- HashMap.lookup blockName (blocks func)
        let instrs = map (\name -> hml (functionInstructions func) name "getBefore" ) (blockInstructions block)
        index <- elemIndex instr instrs
        return $ take index instrs
    of
        Just a -> a
        Nothing -> []

getInstructionParent :: VFunction -> VInstruction -> String
getInstructionParent func instr =
    let f :: String -> Bool = (\instr2 -> instr2 == getName instr)
        x :: [VBlock] = filter (\block -> any (True==) $ map f $ blockInstructions block) (HashMap.elems $ blocks func)
        in case x of
            [y] -> getName y
            _ -> ""

blockToString :: (HashMap.Map String VInstruction) -> VBlock -> String
blockToString hm (VBlock _ name instr pd sc) =
  " " ++ name ++ ":\t\t\t\t\t" ++ (show pd) ++ "|" ++ (show sc) ++ "\n" ++ (foldl (\acc x -> acc ++ "    " ++ (
        case HashMap.lookup x hm of
          Just a -> x ++ " = " ++ (show a) ++ "\n"
          Nothing -> "INVALID_INST("++name++")\n"
        )) "" instr)

getValues :: HashMap.Map String VBlock -> [String] -> [VBlock]
getValues hm [] = []
getValues hm (idx:keys) =
  let lk :: Maybe VBlock = HashMap.lookup idx hm
      val :: [VBlock] = case lk of
        Nothing -> []
        Just a -> [a]
      in val ++ ( getValues hm keys )

instance Show VFunction where
  show (VFunction functionName returnType arguments functionInstructions blocks blockOrder) =
    "def " ++ (show returnType) ++ " "++ functionName ++ (show arguments) ++ "\n" ++ ( foldl (\acc x -> acc ++ (blockToString functionInstructions x)) "" (getValues blocks blockOrder) ) ++ "\n"

instance Value VFunction where
  getType _ (VFunction _ returnType arguments _ _ _ ) = TFunction returnType arguments

instance Namable VFunction where
  getName func = (functionName func)

data VBlock            = VBlock {
  blockFunctionName :: String,
  blockName         :: String,
  blockInstructions :: [String],
  blockPredecessors :: [String],
  blockSuccessors   :: [String]
} deriving (Eq, Show);

instance Namable VBlock where
  getName block = (blockName block)

data PModule          = PModule {
  functions    :: HashMap.Map String VFunction,
  callouts     :: HashMap.Map String String,
  globals      :: HashMap.Map String (VType, Maybe Int),
  lastId       :: Int
} deriving (Eq);

instance Show PModule where
  show (PModule functions callouts globals _) =
    let cstring   = foldl (\acc (str,_) -> acc ++ "callout " ++ (show str) ++"\n") "" ( HashMap.assocs callouts )
        gstring   = foldl (\acc (str,typ) -> acc ++ "global " ++ (show typ) ++" "++ (show str) ++ "\n") "" ( HashMap.assocs globals )
        fstring   = foldl (\acc (str,func) -> acc ++ (show func) ++ "\n") "" (HashMap.assocs functions)
        in cstring ++ "\n" ++ gstring ++ "\n" ++ fstring

uniqueBlockName :: String -> VFunction -> String
uniqueBlockName str func =
  let hm :: HashMap.Map String VBlock = (blocks func)
      inMap :: Bool = HashMap.member str hm in
        case inMap of
          False -> str
          True -> str ++ "." ++ ( show $ head $ filter (\x -> not $ HashMap.member (str ++ "." ++ (show x) ) hm) [1..] )

createID :: PModule -> (String, PModule)
createID pmod =
  let name :: String = "%" ++ (show ((lastId pmod)+1))
      exists :: Int = HashMap.fold (\f acc -> acc + case HashMap.lookup name (functionInstructions f) of Nothing -> 0; _ -> 1) 0 (functions pmod)
      in if exists == 0 then (name, pmod{lastId=((lastId pmod)+1)}) else error (printf "Key %s already exists: MOD\n %s\n" (show name) (show pmod) )


data Context          = Context {
  contextFunctionName :: String,
  contextBlockName    :: String
  {- instructionIndex :: Int -}
} deriving (Eq, Show);

data Builder          = Builder {
  pmod     :: PModule,
  location :: Context,
  debugs   :: [IO()]
};

addDebug :: Builder -> (IO () ) -> Builder
addDebug b a = b{debugs=((debugs b)++[a])}

getFunction :: Builder -> String -> Maybe VFunction
getFunction (Builder pmod _ _) name = HashMap.lookup name (functions pmod)

getInstruction :: Builder -> String -> Maybe VInstruction
getInstruction (Builder pmod (Context fname _) _) name =
  do
    func <- HashMap.lookup fname (functions pmod)
    HashMap.lookup name (functionInstructions func)

getTerminator :: Builder -> Maybe ValueRef
getTerminator builder =
  do
    func <- getFunction builder (contextFunctionName $ location builder)
    block <- HashMap.lookup (contextBlockName $ location builder) $ blocks func
    let lst = blockInstructions block
    final <- if ( length lst )== 0 then Nothing else Just $ last lst
    fv <- HashMap.lookup final $ functionInstructions func
    case fv of
      (VReturn _ _ ) -> Just $ InstRef final
      (VCondBranch _ _ _ _) -> Just $ InstRef final
      (VUncondBranch _ _) -> Just $ InstRef final
      (VUnreachable _) -> Just $ InstRef final
      _ -> Nothing

instance Locationable (String,String) where
  setInsertionPoint (str1,str2) builder = setInsertionPoint (Context str1 str2 ) builder

instance Locationable String where
  setInsertionPoint str builder = setInsertionPoint (Context (contextFunctionName $ location builder) str ) builder

instance Locationable VBlock where
  setInsertionPoint block builder = setInsertionPoint (Context (blockFunctionName block) (blockName block) ) builder

instance Locationable Context where
  setInsertionPoint ctx builder = builder{location=ctx}

appendToBlock :: VInstruction -> VBlock -> VBlock
appendToBlock instr (VBlock a b instructions c d) = VBlock a b (instructions ++ [getName instr]) c d

appendInstruction :: VInstruction -> Builder -> Builder
appendInstruction instr builderm =
  let builder0 = builderm--addDebug builderm $ printf "PAdding instr %s at %s\n" (show instr) (show $ location builderm)
      updated :: Maybe Builder =
        do
          let builder = builder0--addDebug builder0 $ printf "Adding instruction %s\n" (show instr)
          let context = location builder
          let pmod1 = pmod builder
          let fn = contextFunctionName context
          let bn = contextBlockName context
          func <- HashMap.lookup fn (functions pmod1)
          block <- HashMap.lookup bn (blocks func)
          block2 <- return $ appendToBlock instr block
          func2 <- return $ func{blocks=(HashMap.insert bn block2 (blocks func)),functionInstructions=(HashMap.insert (getName instr) instr (functionInstructions func))}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod1)
          return $ builder{pmod=pmod1{functions=functions2}}
      in case updated of
        Just builder2 -> builder2
        Nothing -> builder0

updateBlockF :: VBlock -> VFunction -> VFunction
updateBlockF block2 func = func{blocks=(HashMap.insert (getName block2) block2 (blocks func))}

replaceAndRemoveF :: (VInstruction -> ValueRef) -> VFunction -> VInstruction -> VFunction
replaceAndRemoveF func f inst =
  let f2 = replaceAllUses f inst (func inst)
      f3 = deleteInstruction inst f2
      in f3

replaceAndRemove :: ValueRef -> VFunction -> VInstruction -> VFunction
replaceAndRemove val f inst =
  let f2 = replaceAllUses f inst val
      f3 = deleteInstruction inst f2
      in f3


hml :: Ord a => Show b => Show a => HashMap.Map a b -> a -> String -> b
hml a b l = case HashMap.lookup b a of
  Nothing -> error ( printf "%s: Key %s not in map %s\n" l (show b) (show a) )
  Just c -> c

updateInstructionF :: VInstruction -> VFunction -> VFunction
updateInstructionF instr func =
  let updated :: Maybe VFunction =
        do
          func2 <- return $ func{functionInstructions=(HashMap.insert (getName instr) instr (functionInstructions func))}
          return $ func2
      in case updated of
        Just func2 -> func2
        Nothing -> func

updateInstruction :: VInstruction -> Builder -> Builder
updateInstruction instr builderm =
  let builder0 = builderm--addDebug builderm $ printf "PAdding instr %s at %s\n" (show instr) (show $ location builderm)
      updated :: Maybe Builder =
        do
          let builder = builder0--addDebug builder0 $ printf "Adding instruction %s\n" (show instr)
          let context = location builder
          let pmod1 = pmod builder
          let fn = contextFunctionName context
          let bn = contextBlockName context
          func <- HashMap.lookup fn (functions pmod1)
          block <- HashMap.lookup bn (blocks func)
          block2 <- return $ block
          func2 <- return $ func{blocks=(HashMap.insert bn block2 (blocks func)),functionInstructions=(HashMap.insert (getName instr) instr (functionInstructions func))}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod1)
          return $ builder{pmod=pmod1{functions=functions2}}
      in case updated of
        Just builder2 -> builder2
        Nothing -> builder0

deleteInstruction :: VInstruction -> VFunction -> VFunction
deleteInstruction instr func =
  let deleteFromBlock = \block -> block{blockInstructions=filter (\s -> s /= (getName instr) ) (blockInstructions block) }
      nblocks :: HashMap.Map String VBlock = HashMap.map deleteFromBlock (blocks func)
      ninsts = HashMap.delete (getName instr) (functionInstructions func)
      in func{functionInstructions=ninsts, blocks=nblocks}

createUnaryOp :: {-Operand-} String -> ValueRef -> Builder -> (ValueRef,Builder)
createUnaryOp op operand builder =
  let (name, pmod2) :: (String, PModule) = createID $ pmod builder
      builder2 :: Builder = appendInstruction (VUnOp name op operand) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createBinOp :: String -> ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createBinOp op operand1 operand2 builder =
  let (name, pmod2) :: (String, PModule) = createID $ pmod builder
      builder2 :: Builder = appendInstruction (VBinOp name op operand1 operand2) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createGlobal :: String -> VType -> Maybe Int -> Builder -> (ValueRef, Builder)
createGlobal name op operand1 builder =
  let pmod1 = pmod builder
      pmod2 = pmod1{globals=HashMap.insert name (op,operand1) (globals pmod1)}
      builder2 :: Builder = appendInstruction (VAllocation name op operand1) builder{pmod=pmod2}
      ref :: ValueRef = GlobalRef name in
      (ref, builder2)

createAlloca :: VType -> Maybe Int -> Builder -> (ValueRef, Builder)
createAlloca op operand1 builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VAllocation name op operand1) builder{pmod=pmod2}
      builder3 = builder2--addDebug builder2 $ printf "creating alloca inst ctx:%s %s\n%s\n\n" (show $ location builder2 ) name (show $ pmod builder2)
      ref :: ValueRef = InstRef name in
      (ref, builder3)

maybeIntToInt :: Maybe Int -> Int
maybeIntToInt val = case val of
  Nothing -> 0
  Just v  -> v

zeroMemory :: (ValueRef, Builder) -> VType -> Maybe Int-> Builder
zeroMemory (mem,builder) typ val =
  case val of
    Nothing ->
      case typ of
         TInt   -> snd $ createStore (ConstInt  0) mem builder
         TBool  -> snd $ createStore (ConstBool False) mem builder
         TVoid  -> builder
         x -> addDebug builder $ printf "wtf %s\n" (show x)
    Just rval -> snd $ createZeroInstr mem (rval*(typeSize typ)) builder


createZeroAlloca :: VType -> Maybe Int -> Builder -> (ValueRef, Builder)
createZeroAlloca op len builder0 =
  let (ref, builder) = createAlloca op len builder0
      builder2 = zeroMemory (ref, builder) op len
      in (ref, builder2)

createStore :: ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createStore toStore loc builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VStore name toStore loc) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createLookup :: ValueRef -> Builder -> (ValueRef, Builder)
createLookup loc builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VLookup name loc) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createArrayStore :: ValueRef -> ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createArrayStore toStore array index builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VArrayStore name toStore array index) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createArrayLookup :: ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createArrayLookup array index builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VArrayLookup name array index) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createArrayLen :: ValueRef -> Builder -> (ValueRef, Builder)
createArrayLen array builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VArrayLen name array) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createBoundedArrayLookup :: ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createBoundedArrayLookup array index ar1 =
  let (len, ar2)      = createArrayLen array ar1
      (inBounds, ar3) = createBinOp "u<" index len ar2
      (goodBlock,ar4) = createBlock "inbounds" ar3
      (badBlock,ar5)  = createBlock "outbounds" ar4
      (_,ar6)         = createCondBranch inBounds goodBlock badBlock ar5
      ar7             = setInsertionPoint badBlock ar6
      ar8             = createExit (-1) ar7
      (_,ar9)         = createUnreachable ar8
      ar10            = setInsertionPoint goodBlock ar9
      in createArrayLookup array index ar10

createBoundedArrayStore :: ValueRef -> ValueRef -> ValueRef -> Builder -> (ValueRef, Builder)
createBoundedArrayStore toStore array index ar1 =
  let (len, ar2)      = createArrayLen array ar1
      (inBounds, ar3) = createBinOp "u<" index len ar2
      (goodBlock,ar4) = createBlock "inbounds" ar3
      (badBlock,ar5)  = createBlock "outbounds" ar4
      (_,ar6)         = createCondBranch inBounds goodBlock badBlock ar5
      ar7             = setInsertionPoint badBlock ar6
      ar8             = createExit (-1) ar7
      (_,ar9)         = createUnreachable ar8
      ar10            = setInsertionPoint goodBlock ar9
      in createArrayStore toStore array index ar10


createReturn :: Maybe ValueRef -> Builder -> (ValueRef, Builder)
createReturn retValue builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VReturn name retValue) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createPHINode2 :: (HashMap.Map String ValueRef) -> Builder -> (ValueRef, Builder)
createPHINode2 hmap builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VPHINode name hmap) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createPHINode :: Builder -> (ValueRef, Builder)
createPHINode builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VPHINode name HashMap.empty) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

phiAddIncoming :: ValueRef -> String -> ValueRef -> Builder -> Builder
phiAddIncoming inVal inBlock phi builder =
  case phi of
    (InstRef phiInst) ->
      case getInstruction builder phiInst of
        (Just (VPHINode nam blcks)) ->
           updateInstruction (VPHINode nam (HashMap.insert inBlock inVal blcks)) builder
        _ -> builder
    _ -> builder

phiRemoveBlock :: String -> ValueRef -> Builder -> Builder
phiRemoveBlock inBlock phi builder =
  case phi of
    (InstRef phiInst) ->
      case getInstruction builder phiInst of
        (Just (VPHINode nam blcks)) ->
           updateInstruction (VPHINode nam (HashMap.delete inBlock blcks)) builder
        _ -> builder
    _ -> builder

createCondBranch :: ValueRef -> String -> String -> Builder -> (ValueRef, Builder)
createCondBranch cond trueBranch falseBranch builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      ref :: ValueRef = InstRef name
      ctx = location builder
      builder2Maybe =
        do
          let fn = (contextFunctionName ctx)
          let blockN = (contextBlockName ctx)
          func <- HashMap.lookup fn (functions pmod2)
          block <- HashMap.lookup blockN (blocks func)
          trueBranchBlock <- HashMap.lookup trueBranch (blocks func)
          falseBranchBlock <- HashMap.lookup falseBranch (blocks func)
          let trueBranchBlockPreds = (blockPredecessors trueBranchBlock) ++ [blockN]
          let falseBranchBlockPreds = (blockPredecessors falseBranchBlock) ++ [blockN]
          let trueBranchBlock2 = trueBranchBlock{blockPredecessors=trueBranchBlockPreds}
          let falseBranchBlock2 = falseBranchBlock{blockPredecessors=falseBranchBlockPreds}
          let blockSuccs = (blockSuccessors block) ++ [trueBranch, falseBranch]
          let block2 = block{blockSuccessors=blockSuccs}
          let func2 = func{blocks=(HashMap.update (\_ -> Just block2) blockN (blocks func))}
          let func3 = func2{blocks=(HashMap.update (\_ -> Just trueBranchBlock2) trueBranch (blocks func2))}
          let func4 = func3{blocks=(HashMap.update (\_ -> Just falseBranchBlock2) falseBranch (blocks func3))}
          let pmod3 = pmod2{functions=(HashMap.update (\_ -> Just func4) fn (functions pmod2))}
          return $ builder{pmod=pmod3}
      in case builder2Maybe of
          Just builder2 ->
            let builder3 :: Builder = appendInstruction (VCondBranch name cond trueBranch falseBranch) builder2
                in (ref, builder3)
          Nothing -> (ref, builder)

createUnreachable :: Builder -> (ValueRef, Builder)
createUnreachable builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VUnreachable name) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createExit :: Int -> Builder -> Builder
createExit eval build = snd $ createCalloutCall "exit" [ConstInt $ read $ show eval] build

createUncondBranch :: String -> Builder -> (ValueRef, Builder)
createUncondBranch branch builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      ref :: ValueRef = InstRef name
      ctx = location builder
      builder2Maybe =
        do
          let fn = (contextFunctionName ctx)
          let blockN = (contextBlockName ctx)
          func <- HashMap.lookup fn (functions pmod2)
          block <- HashMap.lookup blockN (blocks func)
          branchBlock <- HashMap.lookup branch (blocks func)
          let branchBlockPreds = (blockPredecessors branchBlock) ++ [blockN]
          let branchBlock2 = branchBlock{blockPredecessors=branchBlockPreds}
          let blockSuccs = (blockSuccessors block) ++ [branch]
          let block2 = block{blockSuccessors=blockSuccs}
          let func2 = func{blocks=(HashMap.update (\_ -> Just block2) blockN (blocks func))}
          let func3 = func2{blocks=(HashMap.update (\_ -> Just branchBlock2) branch (blocks func2))}
          let pmod3 = pmod2{functions=(HashMap.update (\_ -> Just func3) fn (functions pmod2))}
          return $ builder{pmod=pmod3}
      in case builder2Maybe of
          Just builder2 ->
            let builder3 :: Builder = appendInstruction (VUncondBranch name branch) builder2
                in (ref, builder3)
          Nothing -> (ref, builder)

createMethodCall :: String -> [ValueRef] -> Builder -> (ValueRef, Builder)
createMethodCall fname args builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VMethodCall name False fname args) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createCalloutCall :: String -> [ValueRef] -> Builder -> (ValueRef, Builder)
createCalloutCall fname args builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = appendInstruction (VMethodCall name True fname args) builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createZeroInstr :: ValueRef -> Int -> Builder -> (ValueRef, Builder)
createZeroInstr arg size builder =
  let pmod1 = pmod builder
      (name, pmod2) :: (String, PModule) = createID pmod1
      builder2 :: Builder = builder{pmod=pmod2}
      ref :: ValueRef = InstRef name in
      (ref, builder2)

createBlockF :: String -> VFunction -> VFunction
createBlockF str func =
  let str2 = uniqueBlockName str func
      block = VBlock (functionName func) str2 [] [] []
      in func {blocks = HashMap.insert str2 block $ blocks func, blockOrder=(blockOrder func)++[str2]}

removeEmptyBlock :: String -> Builder -> Builder
removeEmptyBlock str builder =
  let updated :: Maybe Builder =
        do
          let pmod1 = pmod builder
          let context = location builder
          let fn = contextFunctionName context
          func <- HashMap.lookup fn (functions pmod1)
          let newBlocks = HashMap.delete str (blocks func)
          func2 <- return $ func{blocks=newBlocks, blockOrder=delete str (blockOrder func)}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod1)
          return $ builder{pmod=pmod1{functions=functions2}}
      in case updated of
        Just builder -> builder
        Nothing -> builder

createBlock :: String -> Builder -> (String, Builder)
createBlock str builder =
  let updated :: Maybe (String,Builder) =
        do
          let pmod1 = pmod builder
          let context = location builder
          let fn = contextFunctionName context
          func <- HashMap.lookup fn (functions pmod1)
          let str2 = uniqueBlockName str func
          block <- return $ VBlock fn str2 [] [] []
          let oldBlocks = blocks func
          let newBlocks = HashMap.insert str2 block oldBlocks
          func2 <- return $ func{blocks=newBlocks, blockOrder=(blockOrder func)++[str2]}
          functions2 <- return $ HashMap.insert fn func2 (functions pmod1)
          return $ (str2, builder{pmod=pmod1{functions=functions2}})
      in case updated of
        Just builder -> builder
        Nothing -> ("",builder)

-- is the instruction pure with respect to the global var s in that do we know for sure that the instruction won't modify s
isPureWRT :: VInstruction -> String -> PModule -> Bool
isPureWRT (VUnOp _ _ _ ) s pm = True
isPureWRT (VBinOp _ _ _ _ ) s pm = True
isPureWRT (VStore _ _ loc) s pm = loc /= GlobalRef s
isPureWRT (VLookup _ _) s pm = True
isPureWRT (VAllocation _ _ _) s pm = True
isPureWRT (VArrayStore _ _ loc _) s pm = loc /= GlobalRef s
isPureWRT (VArrayLookup _ _ _) s pm = True
isPureWRT (VArrayLen _ _) s pm = True
isPureWRT (VReturn _ _) s pm = True
isPureWRT (VCondBranch _ _ _ _) s pm = True
isPureWRT (VUncondBranch _ _) s pm = True
isPureWRT (VMethodCall _ {-isCallout-} True fname args) s pm = all (\x -> x /= (GlobalRef s) ) args
isPureWRT (VMethodCall _ {-isCallout-} False fname args) s pm = ( all (\x -> x /= (GlobalRef s) ) args ) && 
  let fun = hml (functions pm) fname "pureWRT"
      insts = HashMap.elems $ (functionInstructions fun)
      in all (\x -> case x of
                      (VMethodCall _ _ fname2 args2) -> if fname2==fname then True else isPureWRT x s pm
                      _ -> isPureWRT x s pm) insts
isPureWRT (VUnreachable _ ) s pm = True
isPureWRT (VPHINode _ _) s pm = True

-- assume no function exists with name currently
createFunction :: String -> VType -> [VType] -> Builder -> Builder
createFunction str ty1 argTypes builder =
  let pmod1 = pmod builder
      func = VFunction str ty1 argTypes (HashMap.empty) (HashMap.empty) []
      func2 = createBlockF "entry" func
      functions2 = HashMap.insert str func2 (functions pmod1) in
        builder{pmod=pmod1{functions=functions2}}

createCallout :: String -> Builder -> Builder
createCallout str builder =
  let pmod1 = pmod builder
      callouts1 = callouts pmod1
      callouts2 = HashMap.insert str str callouts1
      builder2 = builder--addDebug builder $ printf "Adding callout %s\n" (show str)
      in builder2{pmod=pmod1{callouts=callouts2}}

createPModule :: PModule
createPModule = PModule (HashMap.empty) (HashMap.empty) (HashMap.empty) 0

createBuilder :: Builder
createBuilder = Builder createPModule (Context "" "") []

getBlock :: Builder -> String
getBlock builder = contextBlockName . location $ builder
