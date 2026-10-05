import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_33 :
    (List.ofFn coreChunks174_33).flatten =
      (coreData174.take (coreResources174 33).q).drop 57 := by
  decide +kernel

theorem coreCheck174_33 :
    ∀ c : Fin 1, (coreChunks174_33 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 33)) = true := by
  decide +kernel
#print axioms coreFlatten174_33
#print axioms coreCheck174_33
end Erdos883Verified
