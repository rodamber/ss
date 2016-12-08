open util/ordering[Zober] as ZoberStates

// ------------------------------ ZOBER ----------------------------------------

sig Zober {
    clients: set Client,
    drivers: set Driver,
    bannedDrivers: set (Driver - drivers),
    // cars: set Car,
    // rides: set Ride,
}

pred zoberInit[z: Zober] {
    no z.clients // Req. 5
    no z.drivers // Req. 14
    no z.bannedDrivers
}

fact traces {
    first.zoberInit

    all z: Zober - last | let z' = z.next | 
        some c: Client |
        some d: Driver |
            newClient[z, z', c] or
            newDriver[z, z', d]
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
}

// Req. 3
emailsAreUnique: check {
    all z: Zober, c1, c2: z.clients | 
        c1 != c2 => c1.email != c2.email
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
pred removeClient(z, z': Zober, c: z.clients) {
    z'.clients = z.clients - c
    z'.drivers = z.drivers
    z'.bannedDrivers = z.bannedDrivers
}

// Req. 8
onlyRegisteredClientsMayBeRemoved: check {
    all z, z': Zober, c: Client | 
        removeClient[z, z', c] => c in z.clients
} for 2

pred upgradePlan(z, z': Zober, c: z.clients, c': z'.clients) {
    c.plan in REGULAR
    c'.plan in VIP

    c.name = c'.name
    c.email = c'.email

    z'.clients = z.clients - c + c'
    z'.drivers = z.drivers
    z'.bannedDrivers = z.bannedDrivers
}

pred downgradePlan(z, z': Zober, c: z.clients, c': z'.clients) {
    upgradePlan[z', z, c', c]
}

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
}

// Req. 13
licensesAreUnique: check {
    all z: Zober, d1, d2: z.drivers | 
        d1 != d2 => d1.license != d2.license
}

// Req. 14
noDriversAtTheBeginning: check {
    no ZoberStates/first.drivers
} for 5

// Req. 15
mayOnlyRegisterDriverIfNotYetRegistered: check {
    all z, z': Zober, d: Driver |
        newDriver[z, z', d] => d not in z.drivers
} for 5

pred removeDriver(z, z': Zober, d: z.drivers) {
    newDriver[z', z, d]
}

// Req. 16
onlyRegisteredDriversMayBeRemoved: check {
    all z, z': Zober, d: Driver |
        removeDriver[z, z', d] => d in z.drivers
}

// FIXME: update this when we add cars
pred banDriver(z, z': Zober, d: z.drivers) {
    z'.drivers = z.drivers - d
    z'.bannedDrivers = z.bannedDrivers + d

    z'.clients = z.clients
}

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

sig Car {}

abstract sig ZoberService {}
one sig ZoberY, ZoberWhite extends ZoberService {}

// ------------------------------ RIDES ----------------------------------------

// sig Ride {}


// ------------------------------ UTILS ----------------------------------------


// ------------------------------ RUN ------------------------------------------

pred show { }

run show for 5
