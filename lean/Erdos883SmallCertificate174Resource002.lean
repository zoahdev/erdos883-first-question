import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_2 :
    (List.ofFn coreChunks174_2).flatten =
      (coreData174.take (coreResources174 2).q).drop 20 := by
  decide +kernel

theorem coreCheck174_2 :
    ∀ c : Fin 1, (coreChunks174_2 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 2)) = true := by
  decide +kernel
#print axioms coreFlatten174_2
#print axioms coreCheck174_2
end Erdos883Verified
