import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten31_1 :
    (List.ofFn coreChunks31_1).flatten =
      (coreData31.take (coreResources31 1).q).drop 0 := by
  decide +kernel

theorem coreCheck31_1 :
    ∀ c : Fin 1, (coreChunks31_1 c).all
      (coreResourceRowCheck 29 coreData31 (coreResources31 1)) = true := by
  decide +kernel
#print axioms coreFlatten31_1
#print axioms coreCheck31_1
end Erdos883Verified
