structure Point where
  x: Float
  y: Float
deriving Repr

def Point.distance (p1 p2 : Point) : Float :=
  let dx := p2.x - p1.x
  let dy := p2.y - p1.y
  Float.sqrt (dx * dx + dy * dy)

structure RectangularPrism where
  height: Float
  width: Float
  depth: Float
deriving Repr

def RectangularPrism.volume (p : RectangularPrism) : Float :=
  p.height * p.width * p.depth

example :
  let height := 3.0
  let width := 4.0
  let depth := 5.0
  let prism : RectangularPrism := { height, width, depth }
  prism.volume = (height * width * depth) := by rfl

structure Segment where
  a: Point
  b: Point
deriving Repr

def Segment.length (s : Segment) : Float :=
  Point.distance s.a s.b

example :
  let a := { x := 1.0, y := 2.0 }
  let b := { x := 4.0, y := 6.0 }
  let segment : Segment := { a, b }
  segment.length = Point.distance a b := by rfl
