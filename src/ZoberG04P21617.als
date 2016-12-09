open util/ordering[Zober] as ZoberStates
open util/integer as integer

// ------------------------------ ZOBER ----------------------------------------

sig Zober {
    clients: set Client,
    drivers: set Driver,
    bannedDrivers: set (Driver - drivers),
    cars: set Car,
    rides: set Ride,
}

pred zoberInit[z: Zober] {
    no z.clients       // Req. 5
    no z.drivers       // Req. 14
    no z.bannedDrivers // Req. 14
    no z.cars          // Req. 25
    no z.rides
}

fact traces {
    first.zoberInit
    all z: Zober - last | let z' = z.next | 
        some c, c': Client |
        some d: Driver |
        some car, car': Car |
        some r: Ride |
        some grade: Int |
            newClient[z, z', c]                      or
            removeClient[z, z', c]                   or 
            upgradePlan[z, z', c, c']                or
            downgradePlan[z, z', c, c']              or
            newDriver[z, z', d]                      or
            removeDriver[z, z', d]                   or
            banDriver[z, z', d]                      or
            addCar[z, z', car]                       or
            removeCar[z, z', car]                    or
            addDriverToCar[z, z', car, car', d]      or
            removeDriverFromCar[z, z', car, car', d] or
            upgradeService[z, z', car, car']         or
            downgradeService[z, z', car, car']       or
            newRide[z, z', r]                        or
            cancelRide[z, z', r]                     or
            completeRide[z, z', r, grade]
}

// fact debug_trace {
//     first.zoberInit
//     all z: Zober - last |  let z' = z.next | 
//         some c: Client |
//         // some d: Driver |
//         // some car: Car |
//         // some r: Ride |
//         // some grade: Int |
//              newClient[z, z', c] //or
//              // newDriver[z, z', d] or
//              // addCar[z, z', car] or
//              // newRide[z, z', r]
// }

// ------------------------------ CLIENTS --------------------------------------

sig Name {}
sig Email {}

abstract sig Plan {}
one sig VIP, REGULAR extends Plan {}

sig Client {
    name:  one Name,          // Req. 2
    email: one Email,         // Req. 2
    plan:  one REGULAR + VIP, // Req. 4
}

// Req. 1, 6
pred newClient(z, z': Zober, c: z'.clients - z.clients) {
    c.email not in z.clients.email // Req. 3
    c.plan in REGULAR

    z'.clients       = z.clients + c
    z'.drivers       = z.drivers
    z'.bannedDrivers = z.bannedDrivers
    z'.cars          = z.cars
    z'.rides         = z.rides
}

// Req. 8
pred removeClient(z, z': Zober, c: z.clients - z'.clients) {
    c in z.clients // fixme: I don't know why, but alloy seems to ignore the fact
                   // that c is in z.clients

    z'.clients       = z.clients - c
    z'.drivers       = z.drivers
    z'.bannedDrivers = z.bannedDrivers
    z'.cars          = z.cars
    z'.rides         = z.rides
}

pred upgradePlan(z, z': Zober, c: z.clients, c': z'.clients) {
    c.plan in REGULAR
    c'.plan in VIP

    c.name = c'.name
    c.email = c'.email

    newClient[z, z', c']
    removeClient[z, z', c]
}

pred downgradePlan(z, z': Zober, c: z.clients, c': z'.clients) {
    upgradePlan[z', z, c', c]
}

// Req. 3
emailsAreUnique: check {
    all z: Zober, c, c': z.clients | 
        c != c' => c.email != c'.email
} for 5

// Req. 4
clientPlanIsRegularOrVip: check {
    all z: Zober, c: z.clients | 
        c.plan in REGULAR + VIP
} for 5

// Req. 5
noClientsAtTheBeginning: check {
     no ZoberStates/first.clients
} for 5

// Req. 6
mayOnlyRegisterClientIfNotYetRegistered: check {
    all z, z': Zober, c: Client |
        newClient[z, z', c] => c not in z.clients
} for 5

// Req. 7
clientInitialPlanIsRegular: check {
    all z, z': Zober, c: Client |
        newClient[z, z', c] => c.plan in REGULAR
} for 5

// Req. 8
onlyRegisteredClientsMayBeRemoved: check {
    all z, z': Zober, c: Client | 
        removeClient[z, z', c] => c in z.clients
} for 5

// Req. 9
onlyRegisteredClientsMayBeUpgradedOrDowngraded: check {
    all z, z': Zober, c, c': Client |
        upgradePlan[z, z', c, c'] or downgradePlan[z, z', c, c'] 
            => c in z.clients
} for 5

// Req. 10
onlyRegularsMayBeUpgraded: check {
    all z, z': Zober, c, c': Client |
        upgradePlan[z, z', c, c'] => c.plan in REGULAR
} for 5

// Req. 10
onlyVipsMayBeDowngraded: check {
    all z, z': Zober, c, c': Client |
        downgradePlan[z, z', c, c'] => c.plan in VIP
} for 5

// ------------------------------ DRIVERS --------------------------------------

sig Driver {
    name: one Name,       // Req. 12
    license: one License, // Req. 12
}

sig License {}

// Req. 11
pred newDriver(z, z': Zober, d: z'.drivers - z.drivers) {
    d.license not in z.drivers.license // Req. 13

    z'.clients       = z.clients
    z'.drivers       = z.drivers + d
    z'.bannedDrivers = z.bannedDrivers
    z'.cars          = z.cars
    z'.rides         = z.rides
}

pred removeDriver(z, z': Zober, d: z.drivers - z'.drivers) {
    d in z.drivers // fixme: I don't know why, but alloy seems to ignore the fact
                   // that d is in z.drivers

    z'.clients = z.clients
    z'.drivers = z.drivers - d
    z'.bannedDrivers = z.bannedDrivers
    z'.cars = z.cars - owner.d

    removeDriverFromRegisteredCars[z, z', d]

    // A driver can't be removed if a car he owns has a pending ride.
    // fixme
}

pred banDriver(z, z': Zober, d: z.drivers) {
    z'.drivers = z.drivers - d
    z'.bannedDrivers = z.bannedDrivers + d

    z'.clients = z.clients
    z'.cars = z.cars - owner.d

    removeDriverFromRegisteredCars[z, z', d]

    //fixme
    // if a driver is banned cancel all the rides related with the cars s/he owns

}

// Req. 13
licensesAreUnique: check {
    all z: Zober, d1, d2: z.drivers | 
        d1 != d2 => d1.license != d2.license
} for 5

// Req. 14
noDriversAtTheBeginning: check {
    no ZoberStates/first.drivers
} for 5

// Req. 15
mayOnlyRegisterDriverIfNotYetRegistered: check {
    all z, z': Zober, d: Driver |
        newDriver[z, z', d] => d not in z.drivers
} for 5

// Req. 16
onlyRegisteredDriversMayBeRemoved: check {
    all z, z': Zober, d: Driver |
        removeDriver[z, z', d] => d in z.drivers
} for 5

bannedDriversMayNotDrive: check {
    all z: Zober, d: z.bannedDrivers |
        d not in z.drivers
} for 5

// Req. 17
mayNotAddBannedDriver: check {
    all z, z': Zober, d: Driver |
        newDriver[z, z', d] => d not in z.bannedDrivers
} for 5

// ------------------------------ CARS -----------------------------------------

sig Car {
    owner: one Driver, // Req. 19
    drivers: some Driver, // Req. 20
    service: one (ZoberY + ZoberWhite)
}

abstract sig ZoberService {}
one sig ZoberY, ZoberWhite extends ZoberService {}

pred addCar(z, z': Zober, c: z'.cars - z.cars) {
    // fixme: I don't know why, but alloy seems to ignore the fact that c is
    // not in z.cars
    c not in z.cars

    c.owner in c.drivers                          // Req. 21
    c.drivers in z.drivers                        // Req. 22
    all d: c.drivers | #(z.cars <: drivers).d < 2 // Req. 23
    c.service in ZoberY                           // Req. 26

    z'.cars          = z.cars + c
    z'.clients       = z.clients
    z'.drivers       = z.drivers
    z'.bannedDrivers = z.bannedDrivers
    z'.rides         = z.rides
}

pred removeCar(z, z': Zober, c: z.cars - z'.cars) {
    // fixme: I don't know why, but alloy seems to ignore the fact that c is
    // in z.cars
    c in z.cars

    z'.cars = z.cars - c
    z'.clients = z.clients
    z'.drivers = z.drivers
    z'.bannedDrivers = z.bannedDrivers

    // fixme Req. 39
    // a car cannot be removed from the system if there are pending reservations
    // for this car
}

pred addDriverToCar(z, z': Zober, c: z.cars, c': z'.cars, d: z.drivers) {
    d not in c.drivers
    #c.drivers < 3

    c'.owner = c.owner
    c'.drivers = c.drivers + d

    // fixme: check if this holds now that we've added rides
    // maybe it doesn't because cars can't be removed if there are pending rides
    // for it
    addCar[z, z', c']
    removeCar[z, z', c]
}

pred removeDriverFromCar(z, z': Zober, c: z.cars, c': z'.cars, d: c.drivers) {
    d != c.owner
    addDriverToCar[z', z, c', c, d]
}

pred upgradeService(z, z': Zober, c: z.cars, c': z'.cars) {
    c.service in ZoberY
    c'.service in ZoberWhite

    c'.owner = c.owner
    c'.drivers = c.drivers

    // fixme: check if this holds now that we've added rides
    // maybe it doesn't because cars can't be removed if there are pending rides
    // for it
    addCar[z, z', c']
    removeCar[z, z', c]
}

pred downgradeService(z, z': Zober, c: z.cars, c': z'.cars) {
    upgradeService[z', z, c', c]
}

// Req. 18
mayOnlyRegisterCarIfNotYetRegistered: check {
    all z, z': Zober, c: Car |
        addCar[z, z', c] => c not in z.cars
} for 5

// Req. 19
carsHaveASingleOwner: check {
    all z: Zober, c: z.cars | #c.owner = 1
} for 5

// Req. 20
carsHaveHaveBetween1and3Drivers: check {
    all z: Zober, c: z.cars |
        1 <= #c.drivers and #c.drivers <= 3
} for 5

// Req. 21
carOwnerIsOneOfTheDrivers: check {
    all z: Zober, c: z.cars | 
        c.owner in c.drivers
} for 5

// Req. 22
carDriversMustBeRegistered: check {
    all z: Zober, c: z.cars |
        c.drivers in z.drivers
} for 5

// Req. 23
driverMayNotDriveMoreThanTwoCars: check {
    all z: Zober, d: z.drivers |
        #(z.cars <: drivers).d <= 2
} for 5

// Req. 24
carsProvideZoberYOrZoberWhite: check {
    all c: Car | c.service in ZoberY + ZoberWhite
} for 5

// Req. 25
noCarsAtTheBeginning: check {
    no ZoberStates/first.cars
} for 5

// Req. 26
carInitialServiceIsZoberY: check {
    all z, z': Zober, c: Car |
        addCar[z, z', c] => c.service in ZoberY
} for 5

// Req. 27
onlyRegisteredCarsMayBeRemoved: check {
    all z, z': Zober, c: Car |
        removeCar[z, z', c] => c in z.cars
} for 5

// Req. 28
onlyRegistedDriversMayBeRemovedFromACar: check {
    all z, z': Zober, c, c': Car, d: Driver |
        removeDriverFromCar[z, z', c, c', d] => d in z.drivers
} for 5


// ------------------------------ RIDES ----------------------------------------

sig Ride {
    car: one Car,
    client: one Client,
    service: ZoberY + ZoberWhite,
    beginning: one Int, // fixme: should really use ints or some ordered type?
    end: one Int,
    rate: lone Int
}

pred newRide(z, z': Zober, r: Ride) {
    // For req. 30 we're interested that the car is at least as good as we need.
    r.service = ZoberWhite => r.car.service = ZoberWhite // Req. 30

    r.beginning < r.end  // Req. 31
    carIsAvailable[z, r] // Req. 32

    no r.rate

    r.car in z.cars
    r.client in z.clients

    z'.clients       = z.clients
    z'.drivers       = z.drivers
    z'.bannedDrivers = z.bannedDrivers
    z'.cars          = z.cars
    z'.rides         = z.rides + r
}

pred cancelRide(z, z': Zober, r: z.rides) {
    z'.clients       = z.clients
    z'.drivers       = z.drivers
    z'.bannedDrivers = z.bannedDrivers
    z'.cars          = z.cars
    z'.rides         = z.rides - r
}

pred completeRide(z, z': Zober, r: z.rides, grade: Int) {
    no r.rate

    z'.clients       = z.clients
    z'.drivers       = z.drivers
    z'.bannedDrivers = z.bannedDrivers
    z'.cars          = z.cars
    z'.rides         = z.rides

    z'.rides <: rate = z.rides <: rate + r->grade
}

// Req. 30
carIsAtLeastAsGoodAsWeNeed: check {
    all z: Zober, r: z.rides |
        r.service = ZoberWhite => r.car.service = ZoberWhite
} for 2 but 1 Client, 1 Ride, 1 Car, 1 Driver

// Req. 31
everyRideIsWellFormed: check {
    all z: Zober, r: z.rides |
        r.beginning < r.end
} for 5

// Req. 32
noCarHasOverlappingRides: check {
    all z: Zober, c: z.cars, r, r': car.c |
        r.end < r'.beginning or r'.end < r.beginning
} for 5

// Req. 33
everyCompletedRideHasRating: check {
    all z: Zober, r: z.rides |
        no r.rate => not rideIsCompleted[z, r]
} for 5

// Req. 34
regularClientsMayHaveUpTo2BookedRides: check {
    all z: Zober, c: z.clients |
        c.plan in REGULAR => #(bookedRides[z] <: client).c <= 2
} for 5

// Req. 35
vipClientsOnlyTravelInZoberWhite: check {
    all z: Zober, r: z.rides |
        r.client.plan in VIP => r.service = ZoberWhite
} for 5

// Req. 36
clientsWithBookedRidesMayNotBeRemoved: check {
    all z, z': Zober, r: bookedRides[z] |
        not removeClient[z, z', r.client]
} for 5

// Req. 37
anyNonCompletedRideMayBeCanceled: check {
    all z: Zober, r: bookedRides[z] |
        some z': Zober |
            cancelRide[z, z', r]
} for 5

// Req. 38
bannedDriverHasItsCarsAndRidesRemoved: check {
    all z, z': Zober, d: z.drivers |
        banDriver[z, z', d] => 
            // Should remove the cars owned by the driver
            owner.d not in z'.cars and
            // Remove the rides of cars owned by the driver
            car.owner.d not in z'.rides
} for 5

// Req. 39
carMayNotBeRemovedIfThereAreBookedRidesForIt: check {
    all z, z': Zober, r: bookedRides[z] |
        not removeCar[z, z', r.car]
} for 5

// Req. 40
carOwnerMayNotBeRemovedIfThereAreBookedRidesForCarsHeOwns: check {
    all z, z': Zober, r: bookedRides[z] |
        not removeDriver[z, z', r.car.owner]
} for 5

// ------------------------------ UTILS ----------------------------------------

// Remove driver from all registered cars in the current state.
pred removeDriverFromRegisteredCars(z, z': Zober, d: z.drivers) {
    // This complicated mess is a simple range subtraction.
    // z'.cars <| drivers = z.cars <| drivers |>> d
    z'.cars <: drivers = (z.cars <: drivers) - (z.cars <: drivers :> d)
}

pred carIsAvailable(z: Zober, r: z.rides) {
    all r': z.rides | r.car = r'.car => 
        r.end < r'.beginning or r'.end < r.beginning
}

pred rideIsCompleted(z: Zober, r: z.rides) {
    one r.(z.rides <: rate)
}

fun completedRides(z: Zober): set Ride {
    {r: z.rides | rideIsCompleted[z, r]}
    // {r in z.rides | True}
}

fun bookedRides(z: Zober): set Ride {
    z.rides - completedRides[z]
}

// ------------------------------ RUN ------------------------------------------

pred show { }
run show for 5
