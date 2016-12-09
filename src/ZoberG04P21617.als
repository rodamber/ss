open util/ordering[Zober] as ZoberStates

// ------------------------------ ZOBER ----------------------------------------

sig Zober {
    clients: set Client,
    drivers: set Driver,
    bannedDrivers: set (Driver - drivers),
    cars: set Car,
    // rides: set Ride,
}

pred zoberInit[z: Zober] {
    no z.clients       // Req. 5
    no z.drivers       // Req. 14
    no z.bannedDrivers // Req. 14
    no z.cars          // Req. 25
}

// fact traces {
//     first.zoberInit
//     all z: Zober - last | let z' = z.next | 
//         some c, c': Client |
//         some d: Driver |
//         some car, car': Car |
//             newClient[z, z', c]                      or
//             removeClient[z, z', c]                   or 
//             upgradePlan[z, z', c, c']                or
//             downgradePlan[z, z', c, c']              or
//             newDriver[z, z', d]                      or
//             removeDriver[z, z', d]                   or
//             banDriver[z, z', d]                      or
//             addCar[z, z', car]                       or
//             removeCar[z, z', car]                    or
//             addDriverToCar[z, z', car, car', d]      or
//             removeDriverFromCar[z, z', car, car', d] or
//             upgradeService[z, z', car, car']         or
//             downgradeService[z, z', car, car']
// }

fact debug_trace {
    first.zoberInit
    all z: Zober - last | let z' = z.next | 
        some c: Car |
            some d: Driver |
                addCar[z, z', c] or
                newDriver[z, z', d] or
                removeCar[z, z', c]
}

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

    z'.clients = z.clients + c
    z'.drivers = z.drivers
    z'.bannedDrivers = z.bannedDrivers
    z'.cars = z.cars
}

// Req. 8
pred removeClient(z, z': Zober, c: z.clients - z'.clients) {
    c in z.clients // fixme: I don't know why, but alloy seems to ignore the fact
                   // that c is in z.clients

    z'.clients = z.clients - c
    z'.drivers = z.drivers
    z'.bannedDrivers = z.bannedDrivers
    z'.cars = z.cars
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

    z'.clients = z.clients
    z'.drivers = z.drivers + d
    z'.bannedDrivers = z.bannedDrivers
    z'.cars = z.cars
}

pred removeDriver(z, z': Zober, d: z.drivers - z'.drivers) {
    d in z.drivers // fixme: I don't know why, but alloy seems to ignore the fact
                   // that d is in z.drivers

    z'.clients = z.clients
    z'.drivers = z.drivers - d
    z'.bannedDrivers = z.bannedDrivers
    z'.cars = z.cars - owner.d

    removeDriverFromRegisteredCars[z, z', d]
}

pred banDriver(z, z': Zober, d: z.drivers) {
    z'.drivers = z.drivers - d
    z'.bannedDrivers = z.bannedDrivers + d

    z'.clients = z.clients
    z'.cars = z.cars - owner.d

    removeDriverFromRegisteredCars[z, z', d]
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

    z'.cars = z.cars + c
    z'.clients = z.clients
    z'.drivers = z.drivers
    z'.bannedDrivers = z.bannedDrivers
}

pred removeCar(z, z': Zober, c: z.cars - z'.cars) {
    // fixme: I don't know why, but alloy seems to ignore the fact that c is
    // in z.cars
    c in z.cars

    z'.cars = z.cars - c
    z'.clients = z.clients
    z'.drivers = z.drivers
    z'.bannedDrivers = z.bannedDrivers
}

pred addDriverToCar(z, z': Zober, c: z.cars, c': z'.cars, d: z.drivers) {
    d not in c.drivers
    #c.drivers < 3

    c'.owner = c.owner
    c'.drivers = c.drivers + d

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
// fixme: what about the every part?
onlyRegistedDriversMayBeRemovedFromACar: check {
    all z, z': Zober, c, c': Car, d: Driver |
        removeDriverFromCar[z, z', c, c', d] => d in z.drivers
} for 5


// ------------------------------ RIDES ----------------------------------------

// sig Ride {}


// ------------------------------ UTILS ----------------------------------------

// Remove driver from all registered cars in the current state.
pred removeDriverFromRegisteredCars(z, z': Zober, d: z.drivers) {
    // This complicated mess is a simple range subtraction.
    // z'.cars <| drivers = z.cars <| drivers |>> d
    z'.cars <: drivers = (z.cars <: drivers) - (z.cars <: drivers :> d)
}

// ------------------------------ RUN ------------------------------------------

pred show { }
run show for 5
