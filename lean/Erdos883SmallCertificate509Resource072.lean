import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_72 :
    (List.ofFn coreChunks509_72).flatten =
      (coreData509.take (coreResources509 72).q).drop 134 := by
  decide +kernel

theorem coreCheck509_72 :
    ∀ c : Fin 1, (coreChunks509_72 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 72)) = true := by
  decide +kernel
#print axioms coreFlatten509_72
#print axioms coreCheck509_72
end Erdos883Verified
