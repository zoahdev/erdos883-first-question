import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_45 :
    (List.ofFn coreChunks509_45).flatten =
      (coreData509.take (coreResources509 45).q).drop 89 := by
  decide +kernel

theorem coreCheck509_45 :
    ∀ c : Fin 1, (coreChunks509_45 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 45)) = true := by
  decide +kernel
#print axioms coreFlatten509_45
#print axioms coreCheck509_45
end Erdos883Verified
