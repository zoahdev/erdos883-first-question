import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_35 :
    (List.ofFn coreChunks174_35).flatten =
      (coreData174.take (coreResources174 35).q).drop 48 := by
  decide +kernel

theorem coreCheck174_35 :
    ∀ c : Fin 1, (coreChunks174_35 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 35)) = true := by
  decide +kernel
#print axioms coreFlatten174_35
#print axioms coreCheck174_35
end Erdos883Verified
