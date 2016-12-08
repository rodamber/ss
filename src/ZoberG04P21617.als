open util/ordering[Zober] as ZoberStates

// ------------------------------ ZOBER ----------------------------------------

sig Zober {
    clients: set Client,
    // drivers: set Driver,
    // cars: set Car,
    // rides: set Ride,
}

pred zoberInit[z: Zober] {
    no z.clients // Req. 5
}

fact traces {
    first.zoberInit

    all z: Zober - last | let z' = z.next | some c: Client |
        newClient[z, z', c]
}

// ------------------------------ CLIENTS --------------------------------------

sig Name {}
sig Email {}

abstract sig Plan {}
one sig VIP, REGULAR extends Plan {}

sig Client {
    name:  Name,          // Req. 2
    email: Email,         // Req. 2
    plan:  REGULAR + VIP, // Req. 4
}

// Req. 1, 6
pred newClient(z, z': Zober, c: Client - z.clients) {
    c.email not in z.clients.email // Req. 3
    c.plan in REGULAR

    z'.clients = z.clients + c
}

// Req. 3
emailsAreUnique: check {
    all z: Zober, c1, c2: z.clients | 
        c1 != c2 => c1.email != c2.email
} for 10

// Req. 4
clientPlanIsRegularOrVip: check {
    all z: Zober, c: z.clients | 
        c.plan in REGULAR + VIP
} for 10

// Req. 5
noClientsAtTheBeginning: check {
     no ZoberStates/first.clients
} for 10

// Req. 7
clientInitialPlanIsRegular: check {
    all z: Zober, c: z.next.clients - z.clients | 
        c.plan in REGULAR
} for 10

pred removeClient(z, z': Zober, c: z.clients) {
    z'.clients = z.clients - c
}

// Req. 8
onlyRegisteredClientsMayBeRemoved: check {
    all z: Zober, c: Client | 
        z.next.clients = z.clients - c => c in z.clients
} for 10

pred upgradePlan(z, z': Zober, c: z.clients, c': z'.clients) {
    c.plan in REGULAR
    c'.plan in VIP

    c.name = c'.name
    c.email = c'.email

    z'.clients = z.clients - c + c'
}

pred downgradePlan(z, z': Zober, c: z.clients, c': z'.clients) {
    upgradePlan[z', z, c', c]
}

// Req. 9
onlyRegisteredClientsMayBeUpgradedOrDowngraded: check {
    all z, z': Zober, c, c': Client |
        upgradePlan[z, z', c, c'] or downgradePlan[z, z', c, c'] 
            => c in z.clients
} for 10

// Req. 10
onlyRegularsMayBeUpgraded: check {
    all z, z': Zober, c, c': Client |
        upgradePlan[z, z', c, c'] => c.plan in REGULAR
} for 10

// Req. 10
onlyVipsMayBeDowngraded: check {
    all z, z': Zober, c, c': Client |
        downgradePlan[z, z', c, c'] => c.plan in VIP
} for 10

// ------------------------------ DRIVERS --------------------------------------

// abstract sig ZoberService {}
// one sig ZoberY, ZoberWhite extends ZoberService {}

// sig Ride {}

// sig Driver {}

// sig Car {}

// sig License {}

// ------------------------------ UTILS ----------------------------------------


// ------------------------------ RUN ------------------------------------------

pred show { }

run show for 5
