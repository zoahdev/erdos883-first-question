import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_49 :
    (List.ofFn coreChunks509_49).flatten =
      (coreData509.take (coreResources509 49).q).drop 96 := by
  decide +kernel

theorem coreCheck509_49 :
    ∀ c : Fin 1, (coreChunks509_49 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 49)) = true := by
  decide +kernel
#print axioms coreFlatten509_49
#print axioms coreCheck509_49
end Erdos883Verified
