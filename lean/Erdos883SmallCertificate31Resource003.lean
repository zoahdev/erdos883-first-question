import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten31_3 :
    (List.ofFn coreChunks31_3).flatten =
      (coreData31.take (coreResources31 3).q).drop 7 := by
  decide +kernel

theorem coreCheck31_3 :
    ∀ c : Fin 1, (coreChunks31_3 c).all
      (coreResourceRowCheck 29 coreData31 (coreResources31 3)) = true := by
  decide +kernel
#print axioms coreFlatten31_3
#print axioms coreCheck31_3
end Erdos883Verified
