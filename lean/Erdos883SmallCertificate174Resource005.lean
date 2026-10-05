import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_5 :
    (List.ofFn coreChunks174_5).flatten =
      (coreData174.take (coreResources174 5).q).drop 43 := by
  decide +kernel

theorem coreCheck174_5 :
    ∀ c : Fin 1, (coreChunks174_5 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 5)) = true := by
  decide +kernel
#print axioms coreFlatten174_5
#print axioms coreCheck174_5
end Erdos883Verified
