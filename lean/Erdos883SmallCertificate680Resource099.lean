import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_99 :
    (List.ofFn coreChunks680_99).flatten =
      (coreData680.take (coreResources680 99).q).drop 182 := by
  decide +kernel

theorem coreCheck680_99 :
    ∀ c : Fin 1, (coreChunks680_99 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 99)) = true := by
  decide +kernel
#print axioms coreFlatten680_99
#print axioms coreCheck680_99
end Erdos883Verified
