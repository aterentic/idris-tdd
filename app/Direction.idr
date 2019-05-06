module Direction


public export
data Direction = North | East | South | West

export
turnClockwise : Direction -> Direction
turnClockwise North = East
turnClockwise East = South
turnClockwise South = West
turnClockwise West = North

export
Show Direction where
  show North = "North"
  show East = "East"
  show South = "South"
  show West = "West"
  
