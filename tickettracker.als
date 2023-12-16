abstract sig User {
  userId: Int,
 treshold: Int
}

abstract sig NotificationSent {}

one sig Yes, No extends NotificationSent {}

abstract sig Event {
 eventId: Int,
 price1: Int,
 price2: Int,
 notification: NotificationSent
}

fact EventConstraint {
  all e: Event |
   e.price1 > 0 and e.price2 > 0
}

fact UserConstraint {
 all u: User | 
   u.treshold > 1
}

pred Notification {
  all t: Event, u: User |
    (t.notification = Yes) =>
      t.price1 - t.price2 = u.treshold
}

run Notification for 3 but exactly  5 Event
