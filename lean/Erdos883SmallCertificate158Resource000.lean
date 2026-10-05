import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_0 :
    (List.ofFn coreChunks158_0).flatten =
      (coreData158.take (coreResources158 0).q).drop 0 := by
  decide +kernel

theorem coreCheck158_0 :
    ∀ c : Fin 2, (coreChunks158_0 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 0)) = true := by
  decide +kernel
#print axioms coreFlatten158_0
#print axioms coreCheck158_0
end Erdos883Verified
