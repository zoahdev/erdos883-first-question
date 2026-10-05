import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten31_7 :
    (List.ofFn coreChunks31_7).flatten =
      (coreData31.take (coreResources31 7).q).drop 14 := by
  decide +kernel

theorem coreCheck31_7 :
    ∀ c : Fin 1, (coreChunks31_7 c).all
      (coreResourceRowCheck 29 coreData31 (coreResources31 7)) = true := by
  decide +kernel
#print axioms coreFlatten31_7
#print axioms coreCheck31_7
end Erdos883Verified
