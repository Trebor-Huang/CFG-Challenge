module Main where
import MAlonzo.Code.Eval

main :: IO ()
main = do
    test <- map (=='I') <$> getLine
    print (reify test)
    main
