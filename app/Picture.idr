module Picture


data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double
           
area : Shape -> Double           
area (Triangle x y) = 0.5 * x * y
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x


data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture
             
rectangle : Picture
rectangle = Primitive $ Rectangle 20 10

circle : Picture
circle = Primitive $ Circle 5

triangle : Picture
triangle = Primitive $ Triangle 10 10

testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
                      (Combine 
                        (Translate 35 5 circle) 
                        (Translate 15 25 triangle))


%name Shape shape, shape1, shape2
%name Picture pic, pic1, pic2

pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic1 pic2) = pictureArea pic1 + pictureArea pic2
pictureArea (Rotate x pic) = pictureArea pic
pictureArea (Translate x y pic) = pictureArea pic


export
data Biggest = NoTriangle | Size Double

biggerTriangle : Biggest -> Biggest -> Biggest
biggerTriangle NoTriangle NoTriangle = NoTriangle
biggerTriangle NoTriangle (Size y) = Size y
biggerTriangle (Size x) NoTriangle = Size x
biggerTriangle (Size x) (Size y) = if x > y then Size x else Size y

toBiggest : Shape -> Biggest
toBiggest shape@(Triangle x y) = Size (area shape)
toBiggest (Rectangle x y) = NoTriangle
toBiggest (Circle x) = NoTriangle

biggestTriangle : Picture -> Biggest
biggestTriangle (Primitive shape) = toBiggest shape
biggestTriangle (Combine pic1 pic2) = biggerTriangle (biggestTriangle pic1) (biggestTriangle pic2)
biggestTriangle (Rotate x pic) = biggestTriangle pic
biggestTriangle (Translate x y pic) = biggestTriangle pic

export
example : Biggest
example = biggestTriangle (Combine (Primitive (Triangle 10 10)) (Primitive (Triangle 11 9)))

export
Show Biggest where
  show NoTriangle = "NoTriangle"
  show (Size x) = "Triangle " ++ (show x)

Eq Shape where
  (==) (Triangle x z) (Triangle y w) = x == y && z == w
  (==) (Circle x) (Circle y) = x == y
  (==) (Rectangle x z) (Rectangle y w) = x == y && z == w
  (==) _ _ = False
  
Ord Shape where  
  compare x y = compare (area x) (area y)
  
testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]
