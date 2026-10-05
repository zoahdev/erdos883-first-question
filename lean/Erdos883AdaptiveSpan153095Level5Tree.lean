import Erdos883AdaptiveSpan153095Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength153095_5 : adaptiveNumericSpans153095_5.length = 724 := by decide +kernel
theorem adaptiveSpanEvenCache153095_5 : adaptiveSpanEven153095_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain153095_5 : adaptiveSpanEven153095_5.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanEvenEntries153095_5 : adaptiveSpanEven153095_5.spans = coreEvenSpans 76548 0 adaptiveNumericSpans153095_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache153095_5 : adaptiveSpanWhole153095_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain153095_5 : adaptiveSpanWhole153095_5.domainCheck 76548 = true := by decide +kernel
theorem adaptiveSpanWholeEntries153095_5 : adaptiveSpanWhole153095_5.spans = coreWholeSpans 0 adaptiveNumericSpans153095_5 := by
  decide +kernel
end Erdos883Verified
