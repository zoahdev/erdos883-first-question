import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_45 :
    (List.ofFn coreChunks618_45).flatten =
      (coreData618.take (coreResources618 45).q).drop 99 := by
  decide +kernel

theorem coreCheck618_45 :
    ∀ c : Fin 1, (coreChunks618_45 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 45)) = true := by
  decide +kernel
#print axioms coreFlatten618_45
#print axioms coreCheck618_45
end Erdos883Verified
