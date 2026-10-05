import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_27 :
    (List.ofFn coreChunks158_27).flatten =
      (coreData158.take (coreResources158 27).q).drop 57 := by
  decide +kernel

theorem coreCheck158_27 :
    ∀ c : Fin 1, (coreChunks158_27 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 27)) = true := by
  decide +kernel
#print axioms coreFlatten158_27
#print axioms coreCheck158_27
end Erdos883Verified
