{-|
Module      : Unicode
Description : Unicode constants and utilities
Copyright   : (c) Matthew Amy, 2020
Maintainer  : matt.e.amy@gmail.com
Stability   : experimental
Portability : portable
Note        : import qualified
-}

module Feynman.Util.Unicode(
  subscript,
  sub,
  supscript,
  sup,
  ket,
  bra,
  oplus,
  dot,
  and,
  mapsto,
  langle,
  rangle,
  sum,
  rt2,
  i,
  e,
  x,
  y,
  z,
  dots,
  alpha,
  beta,
  gamma,
  delta,
  zeta,
  omega,
  pi,
  ulambda,
  bullet,
  star,
  setUTF8
  ) where

import Prelude hiding (and, sum, pi)

import Data.FastDigits
import System.IO

{-------------------------------
 Sub & super scripts
 -------------------------------}

-- | Convert a decimal digit to a unicode subscript
subscriptI :: Int -> Char
subscriptI j = case j of
  0 -> '\x2080'
  1 -> '\x2081'
  2 -> '\x2082'
  3 -> '\x2083'
  4 -> '\x2084'
  5 -> '\x2085'
  6 -> '\x2086'
  7 -> '\x2087'
  8 -> '\x2088'
  9 -> '\x2089'
  _ -> error "Impossible"

-- | Convert a decimal digit to a unicode subscript
supscriptI :: Int -> Char
supscriptI j = case j of
  0 -> '\x2070'
  1 -> '\x00B9'
  2 -> '\x00B2'
  3 -> '\x00B3'
  4 -> '\x2074'
  5 -> '\x2075'
  6 -> '\x2076'
  7 -> '\x2077'
  8 -> '\x2078'
  9 -> '\x2079'
  _ -> error "Impossible"

-- | Produce the digits of a number with 0
digits' :: Integer -> [Int]
digits' 0 = [0]
digits' j = map fromIntegral $ digits 10 j

-- | Convert an integer into a unicode subscript
subscript :: Integer -> String
subscript = reverse . map subscriptI . digits'

-- | Add a subscript to a string
sub :: String -> Integer -> String
sub s j = s ++ subscript j

-- | Convert an integer into a unicode superscript
supscript :: Integer -> String
supscript = reverse . map supscriptI . digits'

-- | Add a supscript to a string
sup :: String -> Integer -> String
sup s j = s ++ supscript j

{------------------------------
 Combinators
 ------------------------------}

-- | Build a ket from a string
ket :: String -> String
ket s = "|" ++ s ++ rangle

-- | Build a bra from a string
bra :: String -> String
bra s = langle ++ s ++ "|"

{------------------------------
 Constants
 ------------------------------}

oplus :: String
oplus = "\x2295"

dot :: String
dot = "\x22C5"

and :: String
and = "\x22C0"

mapsto :: String
mapsto = "\x21A6" -- or "\x27FC"

langle :: String
langle = "\x27E8"

rangle :: String
rangle = "\x27E9"

sum :: String
sum = "\x03A3" -- or "\x2211"

rt2 :: String
rt2 = "\x221A\&2"

i :: String
i = "\x1D456"

e :: String
e = "\x212F"

x :: String
x = "\x1D465"

y :: String
y = "\x1D466"
  
z :: String
z = "\x1D467"

dots :: String
dots = "\x22EF"

alpha :: String
alpha = "\x03B1"

beta :: String
beta = "\x03B2"

gamma :: String
gamma = "\x03B3"

delta :: String
delta = "\x03B4"

zeta :: String
zeta = "\x03B6"

omega :: String
omega = "\x03C9"

pi :: String
pi = "\x03C0"

ulambda :: String
ulambda = "\x039B"

bullet :: String
bullet = "\x2022"

star :: String
star = "\x2605"

{------------------------------
 Utilities
 ------------------------------}
-- | Sets output encoding explicitly to UTF8
--
--   Note: for utf8 support in Windows
setUTF8 () = hSetEncoding stdout utf8
