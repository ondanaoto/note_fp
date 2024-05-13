-- # Structures
#check 1.2

#check -454.2123215

#check 0.0

#check 0

#check (0 : Float)

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin

#eval origin.x

#eval origin.y

def addPoints (p1 : Point) (p2 : Point) : Point :=
  {x := p1.x + p2.x, y := p1.y + p2.y}

#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }

def distance (p1 p2 : Point) : Float :=
  Float.sqrt ((p1.x - p2.x)^2.0 + (p1.y - p2.y)^2.0)

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

def origin3D : Point3D := {x := 0.0, y := 0.0, z := 0.0}

-- #check { x := 0.0, y := 0.0 }

#check ({ x := 0.0, y := 0.0 } : Point)

#check { x := 0.0, y := 0.0 : Point}

-- ## Updating Structures

def zeroX' (p : Point) : Point :=
  { x := 0.0, y := p.y}

def zeroX (p : Point) : Point :=
  { p with x := 0 }

def fourAndThree : Point :=
  { x :=4.3, y := 3.4 }

#eval fourAndThree

#eval zeroX fourAndThree

#eval fourAndThree

-- ## Behind the Scenes

#check Point.mk 1.5 2.8

#check (Point.mk)

structure Point' where
  point ::
  x : Float
  y : Float
deriving Repr

#check (Point'.x)
#check (Point'.y)
#check (Point'.point)

#eval origin.x
#eval Point.x origin

#eval "one string".append " and another"

def Point.modifyBoth (f : Float -> Float) (p : Point) : Point :=
  {x := f p.x, y := f p.y}

#eval fourAndThree.modifyBoth Float.floor

-- ## Exercises

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float


def volume (r : RectangularPrism) : Float :=
  r.height * r.width * r.depth

def rectangular : RectangularPrism := { height := 3.0, width := 4.0, depth := 5.0 }
#eval volume rectangular

structure Segment where
  startpoint : Point
  endpoint : Point

def length'' (s : Segment) : Float :=
  distance s.startpoint s.endpoint

def segment : Segment := {startpoint := origin, endpoint := fourAndThree}
#eval length'' segment

#check (RectangularPrism.mk)
#check (RectangularPrism.height)
#check (RectangularPrism.width)
#check (RectangularPrism.depth)

structure Hamster where
  name : String
  fluffy : Bool

#check (Hamster.mk)
#check (Hamster.name)
#check (Hamster.fluffy)

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

#check (Book.makeBook)
#check (Book.title)
#check (Book.author)
#check (Book.price)
