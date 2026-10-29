-- |
-- Module       : Gin.Optimize.Evidence
-- Description  : Standalone Lean obligations for exact-cycle candidate equivalence.
-- Copyright    : (c) 2026 Emily Pillmore
-- License      : BSD-3-Clause
--
-- Maintainer   : Emily Pillmore <emilypi@cohomolo.gy>
-- Stability    : experimental
-- Portability  : non-portable (GHC extensions)
--
-- The generated theorem compares every observable output and the next state
-- of every retained register, universally over inputs and original current
-- state. Surviving registers keep their original types and initial values;
-- omitted registers are projected away. A generic induction lifts the checked
-- transition obligation to all cycles. This does not prove Gin's Lean
-- exporter or HDL lowering. Emitting text is not proof:
-- the caller must run Lean, check axioms and replay the resulting module.
module Gin.Optimize.Evidence
  ( emitEquivalence
  , equivalenceTheoremName
  ) where

import Control.Monad (unless)
import Data.Foldable (traverse_)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Normal
import Gin.Core.Syntax (Name, PrimOp (..), Ty (..), Value (..))
import Gin.Error (GinError, Stage (StNormalize), ginError, withContext)
import Gin.Normalize (checkNormal)

equivalenceTheoremName :: Text
equivalenceTheoremName = "GinOptimization.stream_equivalence"

-- | Emit a closed, universally quantified Lean theorem using only generated
-- identifiers, validated scalar types, numeric literals and fixed primitive
-- spellings. No source identifier, certificate text or arbitrary tactic enters
-- the generated source. Kernel-only finite enumeration is tried only up to
-- twelve input/current-state bits; larger obligations must simplify or fail.
emitEquivalence :: NModule -> NModule -> Either GinError Text
emitEquivalence original candidate = withContext "while generating optimizer equivalence \
  \evidence" $ do
  checkNormal original
  checkNormal candidate
  unless
    (nmInputs original == nmInputs candidate)
    (Left (problem "candidate input interface differs"))
  unless
    (fmap outputType (nmOutputs original) == fmap outputType (nmOutputs candidate))
    (Left (problem "candidate output interface differs"))
  unless
    (nmDomain original == nmDomain candidate)
    (Left (problem "candidate clock domain differs"))
  let originalRegisters = registers original
      candidateRegisters = registers candidate
      originalMap = Map.fromList [(nbName bind, bind) | bind <- originalRegisters]
  traverse_ (checkRegister originalMap) candidateRegisters
  let inputs = nmInputs original
      state originalStates = [(nbName bind, nbTy bind) | bind <- originalStates]
      inputTypes = fmap snd inputs
      outputTypes = fmap noTy (nmOutputs original)
      originalStateTypes = fmap nbTy originalRegisters
      candidateStateTypes = fmap nbTy candidateRegisters
      originalIndices =
        Map.fromList [(nbName bind, index) | (index, bind) <-
          zip [0 :: Int ..] originalRegisters]
      small = sum (fmap typeBits (inputTypes <> originalStateTypes)) <= 12
      scalarVariables = components "s" originalStateTypes <> components "i" inputTypes
      boolVariables = [name | (name, TBool) <- scalarVariables]
      unpack = unpackProduct "s" originalStateTypes <> unpackProduct "i" inputTypes
      branchBools =
        if length boolVariables <= 8
          then fmap (\name -> "cases " <> name <> " <;> ") boolVariables
          else []
      normalizeProof =
        Text.concat branchBools
          <> "simp only [before, after, project, Prod.mk.injEq] <;> bv_normalize (config \
            \:= { acNf := true })"
      finiteProof =
        Text.unlines
          ( ["  | intro s i"]
              <> fmap ("    " <>) unpack
              <> ["    revert " <> Text.unwords (fmap fst scalarVariables) | not (null
                  scalarVariables)]
              <> ["    decide +kernel"]
          )
  projected <-
    traverse
      ( \bind -> case Map.lookup (nbName bind) originalIndices of
          Just index -> Right (projection (length originalRegisters) index "s")
          Nothing -> Left (problem "candidate state projection has no original register")
      )
      candidateRegisters
  initialBefore <- traverse registerInitial originalRegisters
  initialAfter <- traverse registerInitial candidateRegisters
  before <-
    renderFunction
      "before"
      "b"
      "BeforeState"
      inputs
      (state originalRegisters)
      original
      originalRegisters
  after <-
    renderFunction
      "after"
      "a"
      "AfterState"
      inputs
      (state candidateRegisters)
      candidate
      candidateRegisters
  pure
    ( Text.unlines
        [ "import Lean.Elab.Command"
        , "import Lean.Util.CollectAxioms"
        , "import Std.Tactic.BVDecide"
        , "import Init.Data.BitVec.Decidable"
        , "set_option maxRecDepth 4096"
        , "set_option maxHeartbeats 2000000"
        , "set_option linter.unusedVariables false"
        , "namespace GinOptimization"
        , "abbrev Input := " <> productType inputTypes
        , "abbrev Output := " <> productType outputTypes
        , "abbrev BeforeState := " <> productType originalStateTypes
        , "abbrev AfterState := " <> productType candidateStateTypes
        , "def project (s : BeforeState) : AfterState := " <> tuple projected
        , "def initialBefore : BeforeState := " <> tuple initialBefore
        , "def initialAfter : AfterState := " <> tuple initialAfter
        , before
        , after
        , "theorem transition_equivalence : ∀ (s : BeforeState) (i : Input),"
        , "    ((before s i).1, project (before s i).2) = after (project s) i := by"
        , "  first"
        , "  | solve"
        , "    | intro s i"
        , Text.unlines (fmap ("      " <>) unpack)
        , "      " <> normalizeProof
        , if small
            then finiteProof
            else "  | fail \"kernel simplification did not discharge the transition \
              \obligation\""
        , streamInduction
        , "end GinOptimization"
        , axiomCheck
        ]
    )
 where
  outputType output = (noName output, noTy output)
  checkRegister originalMap candidateRegister =
    case Map.lookup (nbName candidateRegister) originalMap of
    Just originalRegister
      | nbTy originalRegister == nbTy candidateRegister
      , NReg originalInitial _ <- nbRhs originalRegister
      , NReg candidateInitial _ <- nbRhs candidateRegister
      , originalInitial == candidateInitial ->
          Right originalRegister
    _ -> Left (problem "candidate register lacks a matching original type and \
      \initialization")
  registerInitial bind = case nbRhs bind of
    NReg value _ -> renderAtom Map.empty (ALit value)
    _ -> Left (problem "invalid register initialization in proof emission")

registers :: NModule -> [NBind]
registers original = [bind | bind@NBind {nbRhs = NReg {}} <- nmBinds original]

typeBits :: Ty -> Integer
typeBits TBool = 1
typeBits (TBitVec width) = toInteger width
typeBits _ = 1000000

renderType :: Ty -> Text
renderType TBool = "Bool"
renderType (TBitVec width) = "BitVec " <> shown width
renderType _ = "False"

renderFunction ::
  Text ->
  Text ->
  Text ->
  [(Name, Ty)] ->
  [(Name, Ty)] ->
  NModule ->
  [NBind] ->
  Either GinError Text
renderFunction name prefix stateType inputs states original retained = do
  let combinational =
        [ bind
        | bind <- nmBinds original
        , case nbRhs bind of
            NReg {} -> False
            _ -> True
        ]
      generated =
        Map.fromList
          [(nbName bind, prefix <> shown index) | (index, bind) <-
            zip [0 :: Int ..] combinational]
      environment = Map.unions [generated, parameters "i" inputs, parameters "s" states]
  definitions <- traverse (renderBind environment) combinational
  outputs <- traverse (renderAtom environment . noAtom) (nmOutputs original)
  next <-
    traverse
      ( \bind -> case nbRhs bind of
          NReg _ atom -> renderAtom environment atom
          _ -> Left (problem "invalid retained state descriptor")
      )
      retained
  pure
    ( Text.unlines
        ( [ "def "
              <> name
              <> " (s : "
              <> stateType
              <> ") (i : Input) : Output × "
              <> stateType
              <> " :="
          ]
            <> fmap ("  " <>) definitions
            <> ["  (" <> tuple outputs <> ", " <> tuple next <> ")"]
        )
    )
 where
  parameters variable values =
    Map.fromList
      [ (source, projection (length values) index variable)
      | (index, (source, _)) <- zip [0 :: Int ..] values
      ]
  renderBind environment bind = do
    result <- case nbRhs bind of
      NPrim op atoms -> traverse (renderAtom environment) atoms >>= renderPrimitive op
      NMux c a b -> do
        condition <- renderAtom environment c
        yes <- renderAtom environment a
        no <- renderAtom environment b
        pure ("if " <> condition <> " then " <> yes <> " else " <> no)
      NAtom atom -> renderAtom environment atom
      NReg {} -> Left (problem "unexpected register in combinational proof definitions")
    identifier <- lookupName environment (nbName bind)
    pure ("let " <> identifier <> " : " <> renderType (nbTy bind) <> " := " <> result)

-- Right-nested products use the scalar directly for a singleton. Numeric
-- projections ensure source names can never become executable Lean syntax.
projection :: Int -> Int -> Text -> Text
projection count index variable
  | count <= 1 = variable
  | index == 0 = "(" <> variable <> ").1"
  | otherwise = projection (count - 1) (index - 1) ("(" <> variable <> ").2")

components :: Text -> [Ty] -> [(Text, Ty)]
components _ [] = []
components prefix [ty] = [(prefix, ty)]
components prefix types = [(prefix <> shown index, ty) | (index, ty) <-
  zip [0 :: Int ..] types]

unpackProduct :: Text -> [Ty] -> [Text]
unpackProduct prefix [] = ["cases " <> prefix]
unpackProduct _ [_] = []
unpackProduct prefix types =
  [ "rcases "
      <> prefix
      <> " with ⟨"
      <> Text.intercalate ", " (fmap fst (components prefix types))
      <> "⟩"
  ]

streamInduction :: Text
streamInduction =
  Text.unlines
    [ "def runState {σ ι : Type} (step : σ → ι → σ) (initial : σ) (inputs : Nat → ι) : \
      \Nat → σ"
    , "  | 0 => initial"
    , "  | t + 1 => step (runState step initial inputs t) (inputs t)"
    , "theorem project_runState {σ τ ι : Type}"
    , "    (stepS : σ → ι → σ) (stepT : τ → ι → τ) (projection : σ → τ)"
    , "    (initialS : σ) (initialT : τ)"
    , "    (hinit : projection initialS = initialT)"
    , "    (hstep : ∀ s i, projection (stepS s i) = stepT (projection s) i)"
    , "    (inputs : Nat → ι) (t : Nat) :"
    , "    projection (runState stepS initialS inputs t) = runState stepT initialT \
      \inputs t := by"
    , "  induction t with"
    , "  | zero => exact hinit"
    , "  | succ t ih => simp only [runState]; rw [hstep, ih]"
    , "def stepBefore (s : BeforeState) (i : Input) : BeforeState := (before s i).2"
    , "def stepAfter (s : AfterState) (i : Input) : AfterState := (after s i).2"
    , "theorem initial_refinement : project initialBefore = initialAfter := rfl"
    , "theorem step_refinement (s : BeforeState) (i : Input) :"
    , "    project (stepBefore s i) = stepAfter (project s) i :="
    , "  congrArg Prod.snd (transition_equivalence s i)"
    , "theorem output_refinement (s : BeforeState) (i : Input) :"
    , "    (before s i).1 = (after (project s) i).1 :="
    , "  congrArg Prod.fst (transition_equivalence s i)"
    , "theorem stream_equivalence (inputs : Nat → Input) (t : Nat) :"
    , "    (before (runState stepBefore initialBefore inputs t) (inputs t)).1 ="
    , "    (after (runState stepAfter initialAfter inputs t) (inputs t)).1 := by"
    , "  have hs := project_runState stepBefore stepAfter project initialBefore \
      \initialAfter"
    , "    initial_refinement step_refinement inputs t"
    , "  rw [← hs]"
    , "  exact output_refinement _ _"
    ]

-- This fixed command fails elaboration when the theorem transitively depends
-- on anything beyond Gin's existing axiom policy. A caller must also replay
-- the compiled module; command success by itself is not kernel validation.
axiomCheck :: Text
axiomCheck =
  Text.unlines
    [ "open Lean in"
    , "run_cmd do"
    , "  let approved : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]"
    , "  for declaration in #[``GinOptimization.transition_equivalence, \
      \``GinOptimization.project_runState,"
    , "      ``GinOptimization.stream_equivalence] do"
    , "    let axioms ← collectAxioms declaration"
    , "    for axiomName in axioms do"
    , "      unless approved.contains axiomName do"
    , "        throwError \"unapproved optimizer proof axiom: {axiomName}\""
    , "#print axioms GinOptimization.stream_equivalence"
    ]

productType :: [Ty] -> Text
productType [] = "Unit"
productType [ty] = renderType ty
productType (ty : rest) = "(" <> renderType ty <> " × " <> productType rest <> ")"

tuple :: [Text] -> Text
tuple [] = "()"
tuple [value] = value
tuple (value : rest) = "(" <> value <> ", " <> tuple rest <> ")"

lookupName :: Map Name Text -> Name -> Either GinError Text
lookupName environment name =
  maybe
    (Left (problem "undefined wire in proof emission"))
    Right
    (Map.lookup name environment)

renderAtom :: Map Name Text -> Atom -> Either GinError Text
renderAtom environment (AVar name) = lookupName environment name
renderAtom _ (ALit (VBool value)) = Right (if value then "true" else "false")
renderAtom _ (ALit (VBV width value)) =
  Right ("(BitVec.ofNat " <> shown width <> " " <> shown value <> ")")
renderAtom _ _ = Left (problem "non-scalar literal in proof emission")

renderPrimitive :: PrimOp -> [Text] -> Either GinError Text
renderPrimitive op operands = case (op, operands) of
  (BoolAnd, [a, b]) -> binary "&&" a b
  (BoolOr, [a, b]) -> binary "||" a b
  (BoolXor, [a, b]) -> binary "^^" a b
  (BoolEq, [a, b]) -> binary "==" a b
  (BoolNot, [a]) -> unary "!" a
  (BvAdd, [a, b]) -> binary "+" a b
  (BvSub, [a, b]) -> binary "-" a b
  (BvMul, [a, b]) -> binary "*" a b
  (BvNeg, [a]) -> unary "-" a
  (BvAnd, [a, b]) -> binary "&&&" a b
  (BvOr, [a, b]) -> binary "|||" a b
  (BvXor, [a, b]) -> binary "^^^" a b
  (BvNot, [a]) -> unary "~~~" a
  (BvShl amount, [a]) -> Right ("(" <> a <> " <<< (" <> shown amount <> " : Nat))")
  (BvLshr amount, [a]) -> Right ("(" <> a <> " >>> (" <> shown amount <> " : Nat))")
  (BvEq, [a, b]) -> binary "==" a b
  (BvUlt, [a, b]) -> Right ("(" <> a <> ").ult (" <> b <> ")")
  (BvUle, [a, b]) -> Right ("(" <> a <> ").ule (" <> b <> ")")
  (BvConcat, [a, b]) -> Right ("(" <> a <> ").append (" <> b <> ")")
  (BvExtract hi lo, [a]) ->
    Right ("(" <> a <> ").extractLsb' " <> shown lo <> " " <> shown (hi - lo + 1))
  (BvZext width, [a]) -> Right ("(" <> a <> ").setWidth " <> shown width)
  (BvOfBool, [a]) -> Right ("BitVec.ofBool (" <> a <> ")")
  _ -> Left (problem "unsupported primitive or arity in proof emission")
 where
  binary operator a b = Right ("(" <> a <> " " <> operator <> " " <> b <> ")")
  unary operator a = Right ("(" <> operator <> "(" <> a <> "))")

problem :: Text -> GinError
problem = ginError StNormalize

shown :: Show a => a -> Text
shown = Text.pack . show
