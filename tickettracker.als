one sig Text {}
one sig EncryptedText {}

sig User {
  userId: Int,
  userName: Text,
  password: EncryptedText,
 criteria: Int,
 criteriaCurrency: Text,
 email: Text,
 notiFrom: some Ticket
}

abstract sig NotificationSent {}

one sig Yes, No extends NotificationSent {}

sig Ticket {
 eventId: Int,
 price1: Int,
 price2: Int,
 notification: NotificationSent,
 source: one DataScraper
}

one sig Dashboard {
  tickets: some Ticket,
  currentUser: one User,
  scheduler: one Scheduler
}

one sig TicketDatabase{
  tickets: some Ticket
}

one sig Scheduler{
  
}

sig DataScraper{
   belong_to: set Scheduler
}

fact TicketConstraint {
  all e: Ticket |
   e.price1 > 0 and e.price2 > 0
}

fact TicketSourceConstraint {
  all t: Ticket | some s: DataScraper | t.source = s
}

fact DSContraint {
 all d: DataScraper | some s: Scheduler | d.belong_to = s
}

fact Notification {
  all t: Ticket |
    (t.notification = Yes) =>
      some u: User | some n: u.notiFrom | t = n
}

fact ValidNotif {
  all u: User |
     all t: u.notiFrom | (t.price1 - t.price2) >= u.criteria
}


assert CheckNotif {
  all t: Ticket |
      (t.notification = Yes) =>
          all u: User |
               (t in u.notiFrom) =>
                   (t.price1 - t.price2) >= u.criteria
}

pred CriteriaOneOrMore {
 all u: User | 
   u.criteria > 6
}

pred CriteriaZero {
 all u: User | 
   u.criteria <1
}

pred NotifSent {
  some t: Ticket |
    t.notification = Yes
}

assert ValidSample {
   all u: User | 
    u.criteria < 1 implies
   NotifSent
}

assert InvalidSample {
 all u: User | 
   u.criteria > 6 implies
 NotifSent
}

assert NoNotificationHighCriteria {
 // all u: User | u.criteria > 6 implies no t: u.notiFrom | t.notification = Yes
all u: User | u.criteria > 6 implies
 no t: Ticket |
      (t.notification = Yes) =>
          all u: User |
               (t in u.notiFrom) =>
                   (t.price1 - t.price2) >= u.criteria
}

// Asserting that notification should be sent when all user criteria are below 0
assert NotificationLowCriteria {
  all u: User | u.criteria < 0 implies 
 some t: Ticket |
      (t.notification = Yes) =>
          all u: User |
               (t in u.notiFrom) =>
                   (t.price1 - t.price2) >= u.criteria
}


// TODO: tambah kasus dimana assertion salah

//run CriteriaZero for 5 Ticket, 5 User, 3 DataScraper

check InvalidSample
check ValidSample

check NoNotificationHighCriteria

check NotificationLowCriteria
