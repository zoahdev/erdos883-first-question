import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_7 :
    (List.ofFn coreChunks174_7).flatten =
      (coreData174.take (coreResources174 7).q).drop 0 := by
  decide +kernel

theorem coreCheck174_7 :
    ∀ c : Fin 2, (coreChunks174_7 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 7)) = true := by
  decide +kernel
#print axioms coreFlatten174_7
#print axioms coreCheck174_7
end Erdos883Verified
