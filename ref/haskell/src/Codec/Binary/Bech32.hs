module Codec.Binary.Bech32
  ( bech32Encode
  , bech32Decode
  , toBase32
  , toBase256
  , segwitEncode
  , segwitDecode
  , Word5()
  , word5
  , fromWord5
  ) where

import Control.Monad (guard)
import qualified Data.Array as Arr
import Data.Bits (Bits, unsafeShiftL, unsafeShiftR, (.&.), (.|.), xor, testBit)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Char (toLower, toUpper)
import Data.Foldable (foldl')
import Data.Ix (Ix(..))
import Data.Maybe (fromJust)
import Data.Word (Word8)

type HRP = BS.ByteString
type Data = [Word8]

(.>>.), (.<<.) :: Bits a => a -> Int -> a
(.>>.) = unsafeShiftR
(.<<.) = unsafeShiftL

newtype Word5 = UnsafeWord5 Word8
              deriving (Eq, Ord)

instance Ix Word5 where
  range (UnsafeWord5 m, UnsafeWord5 n) = map UnsafeWord5 $ range (m, n)
  index (UnsafeWord5 m, UnsafeWord5 n) (UnsafeWord5 i) = index (m, n) i
  inRange (m,n) i = m <= i && i <= n

word5 :: Integral a => a -> Word5
word5 x = UnsafeWord5 ((fromIntegral x) .&. 31)
{-# INLINE word5 #-}
{-# SPECIALIZE INLINE word5 :: Word8 -> Word5 #-}

fromWord5 :: Num a => Word5 -> a
fromWord5 (UnsafeWord5 x) = fromIntegral x
{-# INLINE fromWord5 #-}
{-# SPECIALIZE INLINE fromWord5 :: Word5 -> Word8 #-}

charset :: Arr.Array Word5 Char
charset = Arr.listArray (UnsafeWord5 0, UnsafeWord5 31) "qpzry9x8gf2tvdw0s3jn54khce6mua7l"

charsetMap :: Char -> Maybe Word5
charsetMap c | inRange (Arr.bounds inv) upperC = inv Arr.! upperC
             | otherwise = Nothing
  where
    upperC = toUpper c
    inv = Arr.listArray ('0', 'Z') (repeat Nothing) Arr.// (map swap (Arr.assocs charset))
    swap (a, b) = (toUpper b, Just a)

bech32Polymod :: [Word5] -> Word
bech32Polymod values = foldl' go 1 values .&. 0x3fffffff
  where
    go chk value = foldl' xor chk' [g | (g, i) <- zip generator [25..], testBit chk i]
      where
        generator = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
        chk' = chk .<<. 5 `xor` (fromWord5 value)

bech32HRPExpand :: HRP -> [Word5]
bech32HRPExpand hrp = map (UnsafeWord5 . (.>>. 5)) (BS.unpack hrp) ++ [UnsafeWord5 0] ++ map word5 (BS.unpack hrp)

bech32CreateChecksum :: HRP -> [Word5] -> [Word5]
bech32CreateChecksum hrp dat = [word5 (polymod .>>. i) | i <- [25,20..0]]
  where
    values = bech32HRPExpand hrp ++ dat
    polymod = bech32Polymod (values ++ map UnsafeWord5 [0, 0, 0, 0, 0, 0]) `xor` 1

bech32VerifyChecksum :: HRP -> [Word5] -> Bool
bech32VerifyChecksum hrp dat = bech32Polymod (bech32HRPExpand hrp ++ dat) == 1

bech32Encode :: HRP -> [Word5] -> Maybe BS.ByteString
bech32Encode hrp dat = do
    let dat' = dat ++ bech32CreateChecksum hrp dat
        rest = map (charset Arr.!) dat'
        result = BSC.concat [hrp, BSC.pack "1", BSC.pack rest]
    guard $ BS.length result <= 90
    return result

bech32Decode :: BS.ByteString -> Maybe (HRP, [Word5])
bech32Decode bech32 = do
    guard $ BS.length bech32 <= 90
    guard $ BSC.map toUpper bech32 == bech32 || BSC.map toLower bech32 == bech32
    let (hrp, dat) = BSC.breakEnd (== '1') $ BSC.map toLower bech32
    guard $ BS.length dat >= 6
    hrp' <- BSC.stripSuffix (BSC.pack "1") hrp
    guard $ BS.all (\char -> char >= 33 && char <= 126) hrp'
    dat' <- mapM charsetMap $ BSC.unpack dat
    guard $ bech32VerifyChecksum hrp' dat'
    return (hrp', take (BS.length dat - 6) dat')

convertBits :: [Word] -> Int -> Int -> Bool -> Maybe [Word]
convertBits dat frombits tobits pad = fmap (concat . reverse) $ go dat 0 0 []
  where
    go :: [Word] -> Word -> Int -> [[Word]] -> Maybe [[Word]]
    go [] acc bits result = do
        let padValue = (acc .<<. (tobits - bits)) .&. maxv
        if pad
        then if bits /= 0
             then return $ [padValue] : result
             else return result
        else do
            guard $ bits < frombits && padValue == 0
            return result
    go (value:dat') acc bits result = go dat' acc' (bits' `rem` tobits) (result':result)
      where
        acc' = (acc .<<. frombits) .|. fromIntegral value
        bits' = bits + frombits
        result' = [(acc' .>>. b) .&. maxv | b <- [bits'-tobits,bits'-2*tobits..0]]
    maxv = (1 .<<. tobits) - 1
{-# INLINE convertBits #-}

toBase32 :: [Word8] -> [Word5]
toBase32 dat = map word5 $ fromJust $ convertBits (map fromIntegral dat) 8 5 True

toBase256 :: [Word5] -> Maybe [Word8]
toBase256 dat = fmap (map fromIntegral) $ convertBits (map fromWord5 dat) 5 8 False

segwitDecode :: HRP -> BS.ByteString -> Maybe (Word8, Data)
segwitDecode hrp addr = do
    (hrp', dat) <- bech32Decode addr
    guard $ (hrp == hrp') && not (null dat)
    let (UnsafeWord5 witver : datBase32) = dat
    decoded <- toBase256 datBase32
    guard (witver <= 16)
    if witver == 0
        then guard (length decoded == 20 || length decoded == 32)
        else guard (length decoded >= 2 && length decoded <= 40)
    return (witver, decoded)

segwitEncode :: HRP -> Word8 -> Data -> Maybe BS.ByteString
segwitEncode hrp witver witprog = do
    guard $ witver <= 16
    bech32Encode hrp $ UnsafeWord5 witver : toBase32 witprog
