import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_99 :
    (List.ofFn coreChunks618_99).flatten =
      (coreData618.take (coreResources618 99).q).drop 252 := by
  decide +kernel

theorem coreCheck618_99 :
    ∀ c : Fin 1, (coreChunks618_99 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 99)) = true := by
  decide +kernel
#print axioms coreFlatten618_99
#print axioms coreCheck618_99
end Erdos883Verified
