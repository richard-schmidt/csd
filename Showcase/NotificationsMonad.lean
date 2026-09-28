namespace NotificationsMonad

inductive Domain where
| Catalog
| Orders
| Payments
| Shipping
| Notifications
deriving DecidableEq, Repr

inductive NotificationLevel where
| Critical
| High
| Medium
| Low
deriving DecidableEq, Repr

structure NotificationKind where
  label : String
  level : NotificationLevel
deriving DecidableEq, Repr

structure Notification where
  kind : NotificationKind
  payload : String
deriving DecidableEq, Repr

def DomainNotification := Σ _ : Domain, Notification

def Notify (T : Type) : Type :=
  T × List DomainNotification

def Notify.pure {T : Type} (val : T) : Notify T :=
  (val, [])

def Notify.bind {T T' : Type} (x : Notify T) (f : T -> Notify T') : Notify T' :=
  let (val_x, notifications_x) := x
  let (val_y, notifications_y) := f val_x
  (val_y, notifications_x ++ notifications_y)


instance : Monad Notify where
  pure := Notify.pure
  bind := Notify.bind

structure Endpoint (D: Domain) (InType : Type) (OutType : Type) where
  inner : InType -> OutType × Notification × List DomainNotification
  notify : OutType × Notification × List DomainNotification -> Notify OutType :=
    fun (r, n, upstream_notifications) => (r, [⟨D, n⟩] ++ upstream_notifications)
  call : Notify InType -> Notify OutType := fun request => Notify.bind request (notify ∘ inner)

notation r " ⊸ " e => Endpoint.call e (Notify.pure r)

-- examples

structure ProductEntity where
  id : Int
  price : Int

structure OrderLineEntity where
  id : Int
  orderId : Int
  productId : Int

def PriceChanged : NotificationKind := {label := "PriceChanged", level := NotificationLevel.Low}
def OrderLineRepriced : NotificationKind := {label := "OrderLineRepriced", level := NotificationLevel.High}

structure ChangePriceCommand where
  productId : Int
  price : Int

def changePrice : Endpoint Domain.Catalog ChangePriceCommand Int where
  inner command :=
    let new_price := command.price
    (new_price, {kind := PriceChanged, payload := s!"Product {command.productId} now costs {new_price}"}, [])


structure RepriceOrderLineCommand where
  orderId : Int
  productId : Int
  price : Int

def repriceOrderLine : Endpoint Domain.Orders RepriceOrderLineCommand Bool where
  inner command :=
    let upstream_command : ChangePriceCommand :=
      {
        productId := command.productId
        price := command.price
      }
    let (res_value, upstream_notifications) := upstream_command ⊸ changePrice
    (Bool.true,
    {kind := OrderLineRepriced,
     payload := s!"Product {command.productId} in order {command.orderId} has been repriced to {res_value}"},
      upstream_notifications
    )

def command1 : RepriceOrderLineCommand :=
  {
    orderId := 1
    productId := 2
    price := 3
  }

#eval command1 ⊸ repriceOrderLine

end NotificationsMonad
