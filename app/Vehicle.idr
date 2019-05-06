module Vehicle

public export
data PowerSource = Petrol | Pedal | Electric

export
data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Unicycle : Vehicle Pedal
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  
wheels : Vehicle power -> Nat  
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels (Motorcycle fuel) = 2
wheels Unicycle = 1

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel Bicycle impossible
refuel Unicycle impossible
refuel (Motorcycle fuel) = Motorcycle 50

export
Show (Vehicle powersource) where
  show Bicycle = "Bicycle"
  show (Car fuel) = "Car " ++ (show fuel)
  show (Bus fuel) = "Bus " ++ (show fuel)
  show Unicycle = "Unicycle"
  show (Motorcycle fuel) = "Motorcycle " ++ (show fuel)
  
export
example : Vehicle Petrol
example = refuel (Car 20)
 
