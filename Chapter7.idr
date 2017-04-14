module Chapter7

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

Eq Shape where
  (==) (Triangle x y) (Triangle z w) = x == z && y == w
  (==) (Rectangle x y) (Rectangle z w) = x == z && y == w
  (==) (Circle x) (Circle y) = x == y
  (==) _ _ = False

Ord Shape where
  compare a b = compare (area a) (area b)
