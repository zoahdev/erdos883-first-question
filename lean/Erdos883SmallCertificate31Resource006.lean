import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten31_6 :
    (List.ofFn coreChunks31_6).flatten =
      (coreData31.take (coreResources31 6).q).drop 11 := by
  decide +kernel

theorem coreCheck31_6 :
    ∀ c : Fin 1, (coreChunks31_6 c).all
      (coreResourceRowCheck 29 coreData31 (coreResources31 6)) = true := by
  decide +kernel
#print axioms coreFlatten31_6
#print axioms coreCheck31_6
end Erdos883Verified
