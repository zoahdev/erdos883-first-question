import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_45 :
    (List.ofFn coreChunks680_45).flatten =
      (coreData680.take (coreResources680 45).q).drop 88 := by
  decide +kernel

theorem coreCheck680_45 :
    ∀ c : Fin 1, (coreChunks680_45 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 45)) = true := by
  decide +kernel
#print axioms coreFlatten680_45
#print axioms coreCheck680_45
end Erdos883Verified
