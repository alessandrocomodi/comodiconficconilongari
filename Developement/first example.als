//********CLASS DEFINITIONS********

//assuming date as an int dd-mm-yy
//assuming Int as an int hour,minute
//definition of position
sig Position{
  x: one Int,
  y: one Int,
}
sig Text{

}
abstract sig Boolean{}
sig True extends Boolean{}
sig False extends Boolean{}
//definition of a generic person
abstract sig Person{
  idDoc: one Int,
  currentPosition: lone Position,
}{
  idDoc >0
}
//definition of a user
sig User extends Person{
  email: one Text,
  password: one Text,
}
//definition of a taxi driver
sig TaxiDriver extends Person{
  taxiCode: one Text,
  taxiLicense: one Text,
  seatsAvailable: one Int,
  availability: one Boolean,
}{
  seatsAvailable > 1
}
//definition of a ride
sig Ride{
  driver: one TaxiDriver,
  date: one Int,
  startingPoint: lone Position,
  destinationPoint: some Position,
  users: some User,
  numberOfPeple: one Int,
  isShared: one Boolean,
  startingTime: one Int,
  requests: set Request,
}{
  date > 0
  startingPoint != destinationPoint
  numberOfPeple >= 1
  startingTime > 0
}
//
sig Request{
  date: Int,
  startingPoint: Position,
  destinationPoint: Position,
  user: User,
  people: Int,
  acceptSharing: Boolean,
  time: Int,
}{
  date > 0
  time > 0
  people >= 1
  startingPoint != destinationPoint
}
//definition of the reservation
sig Reservation extends Request{
  prenotationTime: one Int,
  prenotationDate: one Int,

}{
  prenotationTime >0
  prenotationDate >0
  prenotationTime - time >= 2
}
//definition of the queue
sig Queue{
  zone: one Text,
  drivers: set TaxiDriver,
}
//definition of the queue manager
one sig QueueManager{
  queues: set Queue,

}

//*************CONSTRAINTS**********//

//uniqueness of the user by the email
fact uniquenessUser{
  no u1,u2 :User | (u1 != u2 and (u1.email = u2.email))
}
//uniqueness of the taxi driver by the double taxicode, taxi license
fact uniquenessTaxiDriver{
  no t1,t2 :TaxiDriver | (t1 != t2 and (t1.taxiCode = t2.taxiCode or t1.taxiLicense = t2.taxiLicense))
}
//difference between prenotation Int and starting Int of a reservation greater than or euqal to  two hours
fact timeLimitPrenotation{
  all r:Reservation | ((r.prenotationTime - r.time<= 2) and r.prenotationDate = r.date) or r.date <= r.prenotationDate
}
//number of available seats >= number of passengers
fact rightPassengersNumber{
  all r: Ride | r.driver.seatsAvailable >= r.numberOfPeple
}
//shared ride has at least two users
fact sharedRide{
  all r: Ride | ((#r.users > 1 or #r.destinationPoint >1 )=> r.isShared = True )
}
//
fact existanceDestinationAndUser{
  no r:Ride | #r.destinationPoint = 0 or #r.users = 0
}
//
fact taxiAvailbleInQueue{
  all t: TaxiDriver | (t.availability = True) <=>(some q: Queue | t in q.drivers) and (t.availability = False) <=> (no q: Queue | t in q.drivers)
}
//
fact driversAtMostOneQueue {
  all t: TaxiDriver | (lone q: Queue | t in q.drivers)
}

//
fact sharedSeats{
  all r : Ride | sum r.requests.people < r.driver.seatsAvailable
}
//
fact queuesAllStoredInManager{
  all q:Queue | q in QueueManager.queues
}

//********** FUNCTIONS ************

//*****ASSERTIONS************


//
assert moreUsersIfShared{
  no r: Ride | #r.users>1 and r.isShared = False
}
check moreUsersIfShared for 4
//
assert noTaxiNoQueue{
  no t:TaxiDriver | t.availability = True and (no q: Queue | t in q.drivers)
}

check noTaxiNoQueue for 4


//****PREDICATES

pred show(){
  #User > 1
  #Ride > 1
  #TaxiDriver > 1
  #Position > 1
  #Request > 1
  #Queue > 1
  #QueueManager = 1
  #Reservation >= 1
  #{r: Ride | r.isShared = True} > 1
}

pred show1(){}
run show for 3
run show1 for 2
