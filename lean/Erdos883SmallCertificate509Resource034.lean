import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_34 :
    (List.ofFn coreChunks509_34).flatten =
      (coreData509.take (coreResources509 34).q).drop 68 := by
  decide +kernel

theorem coreCheck509_34 :
    ∀ c : Fin 1, (coreChunks509_34 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 34)) = true := by
  decide +kernel
#print axioms coreFlatten509_34
#print axioms coreCheck509_34
end Erdos883Verified
