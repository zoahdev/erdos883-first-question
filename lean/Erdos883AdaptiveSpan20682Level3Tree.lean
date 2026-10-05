import Erdos883AdaptiveSpan20682Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength20682_3 : adaptiveNumericSpans20682_3.length = 430 := by decide +kernel
theorem adaptiveSpanEvenCache20682_3 : adaptiveSpanEven20682_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain20682_3 : adaptiveSpanEven20682_3.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanEvenEntries20682_3 : adaptiveSpanEven20682_3.spans = coreEvenSpans 10341 0 adaptiveNumericSpans20682_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache20682_3 : adaptiveSpanWhole20682_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain20682_3 : adaptiveSpanWhole20682_3.domainCheck 10341 = true := by decide +kernel
theorem adaptiveSpanWholeEntries20682_3 : adaptiveSpanWhole20682_3.spans = coreWholeSpans 0 adaptiveNumericSpans20682_3 := by
  decide +kernel
end Erdos883Verified
