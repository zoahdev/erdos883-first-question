import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_24 :
    (List.ofFn coreChunks174_24).flatten =
      (coreData174.take (coreResources174 24).q).drop 53 := by
  decide +kernel

theorem coreCheck174_24 :
    ∀ c : Fin 1, (coreChunks174_24 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 24)) = true := by
  decide +kernel
#print axioms coreFlatten174_24
#print axioms coreCheck174_24
end Erdos883Verified
