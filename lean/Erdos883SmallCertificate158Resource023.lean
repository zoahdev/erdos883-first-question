import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_23 :
    (List.ofFn coreChunks158_23).flatten =
      (coreData158.take (coreResources158 23).q).drop 45 := by
  decide +kernel

theorem coreCheck158_23 :
    ∀ c : Fin 1, (coreChunks158_23 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 23)) = true := by
  decide +kernel
#print axioms coreFlatten158_23
#print axioms coreCheck158_23
end Erdos883Verified
