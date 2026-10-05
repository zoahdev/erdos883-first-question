import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_77 :
    (List.ofFn coreChunks509_77).flatten =
      (coreData509.take (coreResources509 77).q).drop 152 := by
  decide +kernel

theorem coreCheck509_77 :
    ∀ c : Fin 1, (coreChunks509_77 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 77)) = true := by
  decide +kernel
#print axioms coreFlatten509_77
#print axioms coreCheck509_77
end Erdos883Verified
