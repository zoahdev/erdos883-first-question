import Erdos883AdaptiveSpan22751Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength22751_3 : adaptiveNumericSpans22751_3.length = 442 := by decide +kernel
theorem adaptiveSpanEvenCache22751_3 : adaptiveSpanEven22751_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain22751_3 : adaptiveSpanEven22751_3.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanEvenEntries22751_3 : adaptiveSpanEven22751_3.spans = coreEvenSpans 11376 0 adaptiveNumericSpans22751_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache22751_3 : adaptiveSpanWhole22751_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain22751_3 : adaptiveSpanWhole22751_3.domainCheck 11376 = true := by decide +kernel
theorem adaptiveSpanWholeEntries22751_3 : adaptiveSpanWhole22751_3.spans = coreWholeSpans 0 adaptiveNumericSpans22751_3 := by
  decide +kernel
end Erdos883Verified
