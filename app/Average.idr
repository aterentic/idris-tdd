module Average

||| Calculate the average length of words in a string
||| @str a string containing words separated by whitespace
export
average : (str : String) -> Double
average str = let numWords = wordCount str
                  totalLength = sum (allLengths (words str)) in
                  cast totalLength / cast numWords
              where
                wordCount : String -> Nat
                wordCount str = length (words str)

                allLengths : List String -> List Nat
                allLengths xs = map length xs

export
showAverage : String -> String
showAverage str = "The average word length is: " ++ show (average str) ++ "\n"
