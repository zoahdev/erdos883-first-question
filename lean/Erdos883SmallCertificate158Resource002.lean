import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_2 :
    (List.ofFn coreChunks158_2).flatten =
      (coreData158.take (coreResources158 2).q).drop 19 := by
  decide +kernel

theorem coreCheck158_2 :
    ∀ c : Fin 1, (coreChunks158_2 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 2)) = true := by
  decide +kernel
#print axioms coreFlatten158_2
#print axioms coreCheck158_2
end Erdos883Verified
