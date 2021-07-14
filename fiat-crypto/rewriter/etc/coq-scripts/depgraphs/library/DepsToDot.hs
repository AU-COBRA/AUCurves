#! /usr/bin/env runhaskell
{-# LANGUAGE UnicodeSyntax, ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}

import Data.Graph.Inductive
  (reachable, delEdge, mkGraph, nmap, Edge, Gr, DynGraph, UEdge, LEdge, efilter, LNode, labNodes, Graph, delNodes)
import Data.GraphViz
  (Attributes, toGraphID, color, toLabel, printDotGraph, nonClusteredParams, graphToDot, fmtNode, setID, X11Color(..))
import Data.GraphViz.Attributes.Complete
  (Attribute(URL))
import Data.Text.Lazy (Text, pack, unpack)
import Data.List (nub, elemIndex, isSuffixOf, isPrefixOf, stripPrefix)
import Control.Monad (liftM2)
import Data.Maybe
import System.Environment
import System.Exit
import System.IO
import System.Console.GetOpt
import Prelude hiding ((.))

(.) :: Functor f ⇒ (a → b) → (f a → f b)
(.) = fmap

dropBack :: Int → [a] → [a]
dropBack n = reverse . drop n . reverse

uedge :: LEdge a → Edge
uedge (x, y, _) = (x, y)

nfilter :: Graph gr ⇒ (LNode a → Bool) → gr a b → gr a b
nfilter p g = delNodes (map fst $ filter (not . p) $ labNodes g) g

-- like break, but drops the matching first matching element
breakDropping :: (a → Bool) → [a] → ([a], [a])
breakDropping p l = case break p l of (xs, ys) → (xs, dropWhile p ys)

untransitive :: DynGraph gr ⇒ gr a b → gr a b
untransitive g = efilter (not . redundant . uedge) g
  where redundant e@(from, to) = to `elem` reachable from (delEdge e g)

read_deps :: String → Gr FilePath ()
read_deps input = mkGraph (zip [0..] nodes) edges
  where
    content :: [(FilePath, FilePath)]
    content = do
      (left, _ : right) ← break (==':') . lines input
      liftM2 (,) (words left) (words right)
    nodes :: [FilePath]
    nodes = nub $ map fst content ++ map snd content
    edges :: [UEdge]
    edges = map (\(from, to) →
      (fromJust $ elemIndex from nodes, fromJust $ elemIndex to nodes, ())) content

cut_dotvo :: String → String
cut_dotvo = dropBack 3

tryStripPrefix :: Eq a => [a] → [a] → [a]
tryStripPrefix pre str = fromMaybe str (stripPrefix pre str)

tryStripPostfix :: Eq a => [a] → [a] → [a]
tryStripPostfix pre = reverse . tryStripPrefix (reverse pre) . reverse

-- strip to basename
basename :: Options → String → String
basename opts name = foldr (\(from, to) name' →
                                if from `isPrefixOf` name'
                                then to ++ drop (length from) name'
                                else name')
                           name
                           (optStripPaths opts)


renameCoqDoc :: Options → String → String
renameCoqDoc opts p = foldr (\curPathMap p' →
                                  if physpath curPathMap `isPrefixOf` p'
                                  then libname curPathMap ++ "." ++ drop (length $ physpath curPathMap) p'
                                  else p')
                            p
                            (optLibs opts)

coqDocURL :: Options → String → FilePath → String
coqDocURL opts base p = base
  ++ map (\c → if c == '/' then '.' else c) (renameCoqDoc opts (cut_dotvo p))
  ++ ".html"

label :: Options → FilePath → Attributes
label opts p' =
  [ toLabel (basename opts $ cut_dotvo p)
  , color myColor
--  , LabelFontColor (X11Color color)
  ] ++ maybe [] (\base → [URL (pack $ coqDocURL opts base p)]) (optCoqDocBase opts)
  where
    p = tryStripPrefix "./" p'

    myColor :: X11Color
    myColor = foldr (\(path, new_color) old_color →
                        if path `isPrefixOf` p then new_color else old_color)
                    Green
                    (optColors opts)

makeGraph :: Options → String → Text
makeGraph opts = printDotGraph .
  setID (toGraphID $ optTitle opts) .
  graphToDot (nonClusteredParams {fmtNode = snd}) .
  nmap (label opts).
  untransitive .
  nfilter (isSuffixOf ".vo" . snd) .
  read_deps

data PathMap = PathMap {
  libname :: String,
  physpath :: String
}

canonicalizePath :: String → String
canonicalizePath arg = tryStripPrefix "./" $ (tryStripPostfix "/" arg) ++ "/"

splitOnEq :: String → (String, String)
splitOnEq str = (takeWhile (/= '=') str, dropWhile (== '=') $ dropWhile (/= '=') str)

-- assumes "LIBNAME=PATH"
splitPathMap :: String → PathMap
splitPathMap arg = PathMap {
	      libname = fst arg',
	      physpath = snd arg'
}
  where
    arg' = splitOnEq $ canonicalizePath arg

splitPathRep :: String → (String, String)
splitPathRep arg = ( tryStripPrefix "./" $ fst arg'
                   , tryStripPrefix "./" $ snd arg' )
  where arg' = splitOnEq arg

parseColor :: String → (String, X11Color)
parseColor arg = (tryStripPrefix "./" $ fst arg', read $ snd arg')
  where arg' = splitOnEq arg


data Options = Options {
  optCoqDocBase :: Maybe String,
  optTitle :: String,
  optInput :: IO String,
  optOutput :: String → IO (),
  optLibs :: [PathMap],
  optStripPaths :: [(String,String)],
  optColors :: [(String, X11Color)]
}

defaultOptions :: Options
defaultOptions = Options {
  optCoqDocBase = Nothing,
  optTitle = "",
  optInput = getContents,
  optOutput = putStr,
  optLibs = [],
  optStripPaths = [("theories/",""), ("coq/theories/","coq/"), ("src/","")],
  optColors = []
}

options :: [OptDescr (Options → IO Options)]
options = [
  Option [] ["coqdocbase"] (ReqArg (\arg opt →
    return opt { optCoqDocBase = Just arg }) "URL") "coqdoc base path (include trailing slash)",
  Option ['i'] ["input"] (ReqArg (\arg opt →
    return opt { optInput = readFile arg }) "FILE") "input file, stdin if omitted",
  Option ['o'] ["output"] (ReqArg (\arg opt →
    return opt { optOutput = writeFile arg }) "FILE") "output file, stdout if omitted",
  Option ['t'] ["title"] (ReqArg (\arg opt →
    return opt { optTitle = arg }) "TITLE") "title of the graph page",
  Option ['R'] [] (ReqArg (\arg opt →
    return opt { optLibs = optLibs opt ++ [splitPathMap arg] }) "LIBNAME=PATH") "map physical PATH to logical LIBNAME",
  Option ['s'] ["strip"] (ReqArg (\arg opt →
    return opt { optStripPaths = optStripPaths opt ++ [splitPathRep arg] }) "PATH[=NEWPATH]") "strip out the given physical path prefixes in the display, optionally replacing them with the second argument",
  Option ['c'] ["color"] (ReqArg (\arg opt →
    return opt { optColors = optColors opt ++ [parseColor arg] }) "PATH=COLOR") "how to color things starting with a given path",
  Option ['h'] ["help"] (NoArg (\_ →
    usage >> exitSuccess)) "display this help page"]

usage :: IO ()
usage = do
  prg <- getProgName
  hPutStrLn stderr $ usageInfo ("Usage: " ++ prg ++" [OPTION...]") options
  hPutStrLn stderr "Use dot -Tsvg deps.dot -o deps.svg to render the graph"
  hPutStrLn stderr $ replicate 30 ' ' ++ "This DepsToDot has Super Coq Powers."

main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
   (actions,_,[]) → do
     opts <- foldl (>>=) (return defaultOptions) actions
     input <- optInput opts
     optOutput opts $ unpack $ makeGraph opts $ input
   (_,_,errors) → do
     hPutStrLn stderr $ concat errors
     usage
     exitFailure
