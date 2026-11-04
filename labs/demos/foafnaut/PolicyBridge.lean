import L4Factoidal.UI.PolicyProtocol

/-- The public renderer-independent policy protocol, exported unchanged to WASM. -/
@[export layout_policy_request]
def layoutPolicyRequest (input : String) : String :=
  L4Factoidal.UI.PolicyProtocol.request input
