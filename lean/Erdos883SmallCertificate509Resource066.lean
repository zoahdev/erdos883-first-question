import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_66 :
    (List.ofFn coreChunks509_66).flatten =
      (coreData509.take (coreResources509 66).q).drop 123 := by
  decide +kernel

theorem coreCheck509_66 :
    ∀ c : Fin 1, (coreChunks509_66 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 66)) = true := by
  decide +kernel
#print axioms coreFlatten509_66
#print axioms coreCheck509_66
end Erdos883Verified
