import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_51 :
    (List.ofFn coreChunks509_51).flatten =
      (coreData509.take (coreResources509 51).q).drop 99 := by
  decide +kernel

theorem coreCheck509_51 :
    ∀ c : Fin 1, (coreChunks509_51 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 51)) = true := by
  decide +kernel
#print axioms coreFlatten509_51
#print axioms coreCheck509_51
end Erdos883Verified
