import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_17 :
    (List.ofFn coreChunks158_17).flatten =
      (coreData158.take (coreResources158 17).q).drop 35 := by
  decide +kernel

theorem coreCheck158_17 :
    ∀ c : Fin 1, (coreChunks158_17 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 17)) = true := by
  decide +kernel
#print axioms coreFlatten158_17
#print axioms coreCheck158_17
end Erdos883Verified
