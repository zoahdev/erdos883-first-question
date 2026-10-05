import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten31_0 :
    (List.ofFn coreChunks31_0).flatten =
      (coreData31.take (coreResources31 0).q).drop 0 := by
  decide +kernel

theorem coreCheck31_0 :
    ∀ c : Fin 1, (coreChunks31_0 c).all
      (coreResourceRowCheck 29 coreData31 (coreResources31 0)) = true := by
  decide +kernel
#print axioms coreFlatten31_0
#print axioms coreCheck31_0
end Erdos883Verified
