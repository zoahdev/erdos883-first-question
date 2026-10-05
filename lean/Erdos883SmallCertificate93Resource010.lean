import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_10 :
    (List.ofFn coreChunks93_10).flatten =
      (coreData93.take (coreResources93 10).q).drop 26 := by
  decide +kernel

theorem coreCheck93_10 :
    ∀ c : Fin 1, (coreChunks93_10 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 10)) = true := by
  decide +kernel
#print axioms coreFlatten93_10
#print axioms coreCheck93_10
end Erdos883Verified
