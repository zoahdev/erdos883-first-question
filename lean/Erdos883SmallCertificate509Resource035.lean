import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_35 :
    (List.ofFn coreChunks509_35).flatten =
      (coreData509.take (coreResources509 35).q).drop 69 := by
  decide +kernel

theorem coreCheck509_35 :
    ∀ c : Fin 1, (coreChunks509_35 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 35)) = true := by
  decide +kernel
#print axioms coreFlatten509_35
#print axioms coreCheck509_35
end Erdos883Verified
