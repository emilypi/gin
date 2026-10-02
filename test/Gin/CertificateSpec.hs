module Gin.CertificateSpec (spec) where

import Data.ByteString.Lazy qualified as LBS
import Data.Foldable (for_)
import Data.List (subsequences)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Certificate
import Gin.Core.Check (checkProgram)
import Gin.Core.Json (decodeProgram)
import Gin.Core.Syntax
import Gin.Error
import Gin.Examples (counterProgram, testCertificate)
import Test.Hspec

-- | Lean's three standard axioms.
standardAxioms :: [Text]
standardAxioms = ["propext", "Classical.choice", "Quot.sound"]

-- | A well-formed certificate with the given axiom lists.
cert :: [Text] -> [Text] -> Certificate
cert axioms impl =
  (testCertificate "Counter.counter_correct"){certAxioms = axioms, certImplAxioms = impl}

-- | The default policy extended with extra axioms, as a caller would.
allowing :: [Text] -> CertPolicy
allowing extra = CertPolicy (allowedAxioms defaultPolicy <> Set.fromList extra)

-- | A certificate-stage error whose message mentions every fragment.
rejectedNaming :: [Text] -> Either GinError () -> Expectation
rejectedNaming fragments = \case
  Left e -> do
    errStage e `shouldBe` StCertificate
    for_ fragments $ \f -> Text.unpack (errMessage e) `shouldContain` Text.unpack f
  Right () -> expectationFailure "expected a certificate error, but the certificate was accepted"

nativeAxiom :: Text
nativeAxiom = "Counter.counter_correct._native.bv_decide.ax_1_5"

decodeFixture :: FilePath -> IO Program
decodeFixture path = do
  bytes <- LBS.readFile path
  either (fail . Text.unpack . renderError) pure (decodeProgram bytes)

spec :: Spec
spec = do
  describe "policy constants" $ do
    it "[cert-rules] the default policy allows exactly Lean's three standard axioms" $
      allowedAxioms defaultPolicy `shouldBe` Set.fromList standardAxioms
    it "[cert-rules] sorryAx and the reduction and compiler-trust axioms are always rejected" $
      alwaysRejected
        `shouldBe` Set.fromList
          ["sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"]

  describe "checkCertificate" $ do
    it "[cert-rules] accepts every subset of the standard axioms in both lists" $
      for_ (subsequences standardAxioms) $ \axioms ->
        for_ (subsequences standardAxioms) $ \impl ->
          checkCertificate defaultPolicy (cert axioms impl) `shouldBe` Right ()
    it "[cert-rules] accepts the shared test certificate" $
      checkCertificate defaultPolicy (progCertificate counterProgram) `shouldBe` Right ()
    it "[cert-rules] rejects an empty theorem name" $
      rejectedNaming ["theorem"] $
        checkCertificate defaultPolicy (cert [] []){certTheorem = ""}
    it "[cert-rules] rejects a theorem name that is only whitespace" $
      rejectedNaming ["theorem"] $
        checkCertificate defaultPolicy (cert [] []){certTheorem = " \t\n "}
    it "[cert-rules] rejects an empty statement" $
      rejectedNaming ["statement"] $
        checkCertificate defaultPolicy (cert [] []){certStatement = ""}
    it "[cert-rules] rejects a statement that is only whitespace" $
      rejectedNaming ["statement"] $
        checkCertificate defaultPolicy (cert [] []){certStatement = "   "}
    it "[cert-rules] rejects a non-standard axiom in the proof's axioms" $
      rejectedNaming ["Foo.myAxiom", "axioms"] $
        checkCertificate defaultPolicy (cert ["propext", "Foo.myAxiom"] [])
    it "[cert-rules] rejects a non-standard axiom in the implementation's axioms" $
      rejectedNaming ["Foo.myAxiom", "implAxioms"] $
        checkCertificate defaultPolicy (cert ["propext"] ["Foo.myAxiom"])
    it "[cert-rules] accepts an extra axiom that the caller's policy allows" $
      checkCertificate (allowing ["Foo.myAxiom"]) (cert ["Foo.myAxiom"] ["Foo.myAxiom"])
        `shouldBe` Right ()
    it "[cert-rules] rejects an axiom the default policy allows when the caller's policy does not" $
      rejectedNaming ["propext"] $
        checkCertificate (CertPolicy Set.empty) (cert ["propext"] [])
    it "[cert-rules] rejects every always-rejected axiom even when the policy lists it" $
      for_ (Set.toList alwaysRejected) $ \axiom -> do
        rejectedNaming [axiom] $
          checkCertificate (allowing [axiom]) (cert ["propext", axiom] [])
        rejectedNaming [axiom] $
          checkCertificate (allowing [axiom]) (cert [] [axiom])
    it "[cert-rules] rejects a native-decision axiom even when the policy lists it" $ do
      rejectedNaming [nativeAxiom] $
        checkCertificate (allowing [nativeAxiom]) (cert [nativeAxiom] [])
      rejectedNaming [nativeAxiom] $
        checkCertificate (allowing [nativeAxiom]) (cert [] [nativeAxiom])
    it "[cert-rules] does not treat a name merely containing \"native\" as native-decision" $
      checkCertificate (allowing ["Foo.native_lemma"]) (cert ["Foo.native_lemma"] [])
        `shouldBe` Right ()
    it "[cert-rules] names every offending axiom in one error" $ do
      let result =
            checkCertificate
              defaultPolicy
              (cert ["propext", "sorryAx", "Foo.a"] ["Lean.ofReduceBool", nativeAxiom])
      rejectedNaming ["sorryAx", "Foo.a", "Lean.ofReduceBool", nativeAxiom] result
    it "[cert-rules] does not name allowed axioms as offending" $
      case checkCertificate defaultPolicy (cert ["propext", "sorryAx"] ["Quot.sound"]) of
        Left e -> do
          Text.unpack (errMessage e) `shouldContain` "sorryAx"
          Text.unpack (errMessage e) `shouldNotContain` "propext"
          Text.unpack (errMessage e) `shouldNotContain` "Quot.sound"
        Right () -> expectationFailure "expected sorryAx to be rejected"

  describe "sorry fixture" $ do
    it "[cert-sorry-fixture] decodes, type-checks, and fails only the certificate policy" $ do
      p <- decodeFixture "test/fixtures/ir/sorry.gin.json"
      certAxioms (progCertificate p) `shouldBe` ["propext", "sorryAx"]
      checkProgram p `shouldBe` Right ()
      rejectedNaming ["sorryAx"] (checkCertificate defaultPolicy (progCertificate p))
    it "[cert-sorry-fixture] is rejected even when the caller's policy lists sorryAx" $ do
      p <- decodeFixture "test/fixtures/ir/sorry.gin.json"
      rejectedNaming ["sorryAx"] (checkCertificate (allowing ["sorryAx"]) (progCertificate p))
    it "[cert-sorry-fixture] differs from the counter fixture only in its axioms" $ do
      p <- decodeFixture "test/fixtures/ir/sorry.gin.json"
      let c = progCertificate p
      p{progCertificate = c{certAxioms = ["propext"]}} `shouldBe` counterProgram
