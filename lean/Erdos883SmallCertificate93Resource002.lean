import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_2 :
    (List.ofFn coreChunks93_2).flatten =
      (coreData93.take (coreResources93 2).q).drop 12 := by
  decide +kernel

theorem coreCheck93_2 :
    ∀ c : Fin 1, (coreChunks93_2 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 2)) = true := by
  decide +kernel
#print axioms coreFlatten93_2
#print axioms coreCheck93_2
end Erdos883Verified
