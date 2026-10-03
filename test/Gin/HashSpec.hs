-- | SHA-256 against the FIPS 180-4 / NIST example vectors.
module Gin.HashSpec (spec) where

import Data.ByteString.Char8 qualified as BS8
import Gin.Hash (sha256Hex)
import Test.Hspec

spec :: Spec
spec = describe "sha256Hex" $ do
  it "hashes the empty string" $
    sha256Hex "" `shouldBe` "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  it "hashes \"abc\"" $
    sha256Hex "abc" `shouldBe` "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  it "hashes the 448-bit two-block message" $
    sha256Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
      `shouldBe` "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
  it "hashes one million 'a' characters" $
    sha256Hex (BS8.replicate 1000000 'a')
      `shouldBe` "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
  it "hashes messages at the padding boundaries (55, 56, 63, 64, 65, 119, 120 bytes)" $
    fmap (\n -> sha256Hex (BS8.replicate n 'a')) [55, 56, 63, 64, 65, 119, 120]
      `shouldBe` ["9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318", "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a", "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34", "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb", "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0", "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb", "2f3d335432c70b580af0e8e1b3674a7c020d683aa5f73aaaedfdc55af904c21c"]
