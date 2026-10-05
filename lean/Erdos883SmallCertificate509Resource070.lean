import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_70 :
    (List.ofFn coreChunks509_70).flatten =
      (coreData509.take (coreResources509 70).q).drop 131 := by
  decide +kernel

theorem coreCheck509_70 :
    ∀ c : Fin 1, (coreChunks509_70 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 70)) = true := by
  decide +kernel
#print axioms coreFlatten509_70
#print axioms coreCheck509_70
end Erdos883Verified
