one sig Text {}
one sig EncryptedText {}
one sig Dict {}

one sig User {
  userId: Int,
  userName: Text,
  password: EncryptedText,
 criteria: Int,
 criteriaCurrency: Text,
 email: Text,
 notiFrom: some Ticket
} {
	userId > 0
}

abstract sig NotificationSent {}

one sig Yes, No extends NotificationSent {}

sig Ticket {
 eventId: Int,
 price1: Int,
 price2: Int,
 notification: NotificationSent,
 source: one DataScraper
} {
	this in TicketDatabase.tickets
	eventId > 0
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
	scrapersProfile: Dict
}

one sig Notifier {
	criteriaList: Dict,
	userDB: some User
}

sig DataScraper{
	name: Text,
	startURL: Text,
	concurrentRequest: Int,
   belong_to: set Scheduler,
   dataPipeline: one DataPipeline,
   requestPipeline: RequestPipeline
} {
	this in Ticket.source
}

sig DataPipeline {
	ticketDB: TicketDatabase
} {
	this in DataScraper.dataPipeline
}

sig RequestPipeline {
	proxyList: Text,
	userAgentList: Text
} {
	this in DataScraper.requestPipeline
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
     all t: u.notiFrom | sub[t.price1, t.price2] >= u.criteria 
}

fact NotifYes {
   all t: Ticket | all u: User | (t in u.notiFrom) => t.notification = Yes
}

pred CriteriaOneOrMore {
 all u: User | 
   u.criteria > 5
}

pred CriteriaZero {
 all u: User | 
   u.criteria <1
}

assert NoNotificationHighCriteria {
all u: User | u.criteria > 6 implies
// no t: Ticket |
//      (t.notification = Yes) =>
//          all u: User |
//               (t in u.notiFrom) =>
//                   (t.price1 - t.price2) >= u.criteria
no t: Ticket | t.notification = Yes
}

assert NotificationLowCriteria {
  all u: User | u.criteria < 0 implies 
// some t: Ticket |
//      (t.notification = Yes) =>
//          all u: User |
//               (t in u.notiFrom) =>
//                   (t.price1 - t.price2) >= u.criteria
some t: Ticket | t.notification = Yes
}

fact noDuplicate {
	all t1, t2: Ticket | t1 != t2 =>
		t1.source not in t2.source &&
		t1.eventId not in t2.eventId
	all us1, us2: User | us1 != us2 =>
		us1.userId not in us2.userId


	all rp1, rp2: DataScraper | rp1 != rp2 =>
		rp1.requestPipeline not in rp2.requestPipeline


	#Ticket > 3
}

run CriteriaOneOrMore for 5 Ticket, 5 DataScraper, 3 DataPipeline, 5 RequestPipeline

check NoNotificationHighCriteria

check NotificationLowCriteria
