import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_23 :
    (List.ofFn coreChunks174_23).flatten =
      (coreData174.take (coreResources174 23).q).drop 52 := by
  decide +kernel

theorem coreCheck174_23 :
    ∀ c : Fin 1, (coreChunks174_23 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 23)) = true := by
  decide +kernel
#print axioms coreFlatten174_23
#print axioms coreCheck174_23
end Erdos883Verified
